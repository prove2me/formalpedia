-- Prove2me | solution 1 for TopkisRation.Backlog.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T05:48:47.329928+00:00
-- url     : https://prove2.me/submissions/d6363948-d028-4a89-a67d-c1de44bde325

import Mathlib
import Definitions.Def_TopkisRation_Backlog_Model
import Theorems.Thm_TopkisRation_Levels_theorem_1
import Theorems.Thm_TopkisRation_Levels_lemma_2
import Theorems.Thm_TopkisRation_Levels_criticalLevel_exists

set_option autoImplicit false

namespace T3Aux

open TopkisRation MeasureTheory ProbabilityTheory Filter Topology

variable {n : ℕ}

/-! ### Transfer from the `Backlog` model to the `Levels` model (identical fields) -/

/-- The `Backlog` model viewed as a `Levels` model. -/
def toL (M : Backlog.Model n) : Levels.Model n :=
  ⟨M.k, M.a, M.p, M.h, M.v₁, M.v₂, M.c, M.μ⟩

theorem g_eq (M : Backlog.Model n) : ∀ t, M.g t = (toL M).g t
  | 0 => rfl
  | t + 1 => by
    funext z b
    simp only [Backlog.Model.g, Levels.Model.g]
    rw [g_eq M t]
    rfl

theorem standing (M : Backlog.Model n) (hM : M.Standing) : (toL M).Standing :=
  ⟨hM.a_nonneg, hM.h_convex, hM.h_cont, hM.v₁_convex, hM.v₁_cont, hM.v₂_convex, hM.v₂_cont,
    hM.v₂_slope, hM.p_nonneg, hM.p_mono, hM.μ_prob, hM.μ_nonneg, hM.μ_mean⟩

/-! ### Elementary vector facts -/

theorem sv_nonneg {c : ℝ} (hc : 0 ≤ c) (i : Fin n) : (0 : Fin n → ℝ) ≤ c • Pi.single i (1 : ℝ) := by
  intro k
  by_cases h : k = i
  · subst h; simp [hc]
  · simp [Pi.single_apply, h]

theorem sum_single_eq (e : Fin n → ℝ) : ∑ i, e i • Pi.single i (1 : ℝ) = e := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_shift (B : Fin n → ℝ) (m : Fin n) (ε : ℝ) :
    ∑ i, ((B + ε • Pi.single m (1 : ℝ) : Fin n → ℝ) i) = ∑ i, B i + ε := by
  simp [Finset.sum_add_distrib, Pi.single_apply]

/-- Keep the classes above `m`, zero out the others. -/
def proj (m : Fin n) (x : Fin n → ℝ) : Fin n → ℝ := fun i => if m < i then x i else 0

/-- Positive part, coordinatewise. -/
def pos (x : Fin n → ℝ) : Fin n → ℝ := fun i => max (x i) 0

/-- The coordinate map used by `proj`. -/
def keep (m i : Fin n) (r : ℝ) : ℝ := if m < i then r else 0

theorem proj_nonneg {m : Fin n} {v : Fin n → ℝ} (hv : 0 ≤ v) : 0 ≤ proj m v := by
  intro i
  show (0 : ℝ) ≤ proj m v i
  simp only [proj]
  split_ifs
  · exact hv i
  · exact le_rfl

theorem pos_nonneg (y : Fin n → ℝ) : 0 ≤ pos y := by
  intro i
  show (0 : ℝ) ≤ max (y i) 0
  exact le_max_right _ _

theorem proj_measurable (m : Fin n) : Measurable (proj m : (Fin n → ℝ) → (Fin n → ℝ)) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : m < i
  · simp only [proj, h, if_true]; exact measurable_pi_apply i
  · simp only [proj, h, if_false]; exact measurable_const

theorem keep_measurable (m i : Fin n) : Measurable (keep m i) := by
  by_cases h : m < i
  · have e : keep m i = fun r => r := funext fun r => by simp [keep, h]
    rw [e]; exact measurable_id
  · have e : keep m i = fun _ => 0 := funext fun r => by simp [keep, h]
    rw [e]; exact measurable_const

/-! ### Independence: the joint law of the classes above `m` -/

theorem eq_pi (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν]
    (hν : iIndepFun (fun m (x : Fin n → ℝ) => x m) ν) :
    ν = Measure.pi (fun i => ν.map (fun x => x i)) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (μ := ν) (f := fun m (x : Fin n → ℝ) => x m)
    (fun i => (measurable_pi_apply i).aemeasurable)).mp hν
  calc ν = ν.map (fun x => x) := Measure.map_id'.symm
    _ = _ := h

theorem map_proj_eq (μ μ' : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ']
    (hi : iIndepFun (fun m (x : Fin n → ℝ) => x m) μ)
    (hi' : iIndepFun (fun m (x : Fin n → ℝ) => x m) μ')
    (m : Fin n) (hmarg : ∀ i, m < i → μ'.map (fun x => x i) = μ.map (fun x => x i)) :
    μ.map (proj m) = μ'.map (proj m) := by
  have hproj : (proj m : (Fin n → ℝ) → (Fin n → ℝ)) = fun x i => keep m i (x i) := rfl
  have key : ∀ (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν],
      iIndepFun (fun m (x : Fin n → ℝ) => x m) ν →
      ν.map (proj m) = Measure.pi (fun i => (ν.map (fun x => x i)).map (keep m i)) := by
    intro ν _ hν
    rw [hproj]
    conv_lhs => rw [eq_pi ν hν]
    exact Measure.pi_map_pi (fun i => (keep_measurable m i).aemeasurable)
  rw [key μ hi, key μ' hi']
  congr 1
  funext i
  by_cases h : m < i
  · rw [hmarg i h]
  · have e : keep m i = fun _ => 0 := by funext r; simp [keep, h]
    haveI : IsProbabilityMeasure (μ.map (fun x : Fin n → ℝ => x i)) :=
      Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
    haveI : IsProbabilityMeasure (μ'.map (fun x : Fin n → ℝ => x i)) :=
      Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
    rw [e, Measure.map_const, Measure.map_const, measure_univ, measure_univ]

/-! ### The shift invariance and its consequence -/

/-- `D` is invariant under adding `ε` to the stock and `ε` to the backlog of a class `m ≥ j`. -/
def Inv (D : ℝ → (Fin n → ℝ) → ℝ) (j : Fin n) : Prop :=
  ∀ m : Fin n, j ≤ m → ∀ z : ℝ, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b → ∀ ε : ℝ, 0 ≤ ε →
    D (z + ε) (b + ε • Pi.single m 1) = D z b

/-- The function of the net level `z - Σ b` that an invariant `D` reduces to. -/
noncomputable def Phi (D : ℝ → (Fin n → ℝ) → ℝ) (j : Fin n) (y : ℝ) : ℝ :=
  if 0 ≤ y then D y 0 else D 0 ((-y) • Pi.single j 1)

theorem multi_shift {D : ℝ → (Fin n → ℝ) → ℝ} {j : Fin n} (hD : Inv D j) (e : Fin n → ℝ)
    (he : 0 ≤ e) (hej : ∀ i, i < j → e i = 0) :
    ∀ (S : Finset (Fin n)) (z : ℝ), 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b →
      D (z + ∑ i ∈ S, e i) (b + ∑ i ∈ S, e i • Pi.single i 1) = D z b := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro z _ b _; simp
  | @insert a S haS ih =>
    intro z hz b hb
    rw [Finset.sum_insert haS, Finset.sum_insert haS]
    have hS : 0 ≤ ∑ i ∈ S, e i := Finset.sum_nonneg fun i _ => he i
    have hV : (0 : Fin n → ℝ) ≤ ∑ i ∈ S, e i • Pi.single i 1 :=
      Finset.sum_nonneg fun i _ => sv_nonneg (he i) i
    have e1 : z + (e a + ∑ i ∈ S, e i) = (z + ∑ i ∈ S, e i) + e a := by ring
    have e2 : b + (e a • Pi.single a (1 : ℝ) + ∑ i ∈ S, e i • Pi.single i 1) =
        (b + ∑ i ∈ S, e i • Pi.single i 1) + e a • Pi.single a (1 : ℝ) := by abel
    rw [e1, e2]
    by_cases hja : j ≤ a
    · rw [hD a hja _ (by linarith) _ (add_nonneg hb hV) _ (he a)]
      exact ih z hz b hb
    · rw [hej a (not_le.mp hja)]
      simp only [zero_smul, add_zero]
      exact ih z hz b hb

theorem shift_full {D : ℝ → (Fin n → ℝ) → ℝ} {j : Fin n} (hD : Inv D j) (e : Fin n → ℝ)
    (he : 0 ≤ e) (hej : ∀ i, i < j → e i = 0) (z : ℝ) (hz : 0 ≤ z) (b : Fin n → ℝ)
    (hb : 0 ≤ b) : D (z + ∑ i, e i) (b + e) = D z b := by
  have := multi_shift hD e he hej Finset.univ z hz b hb
  rwa [sum_single_eq e] at this

theorem Phi_form {D : ℝ → (Fin n → ℝ) → ℝ} {j : Fin n} (hD : Inv D j) (w : ℝ) (hw : 0 ≤ w)
    (u : Fin n → ℝ) (hu : 0 ≤ u) (huj : ∀ i, i < j → u i = 0) :
    D w u = Phi D j (w - ∑ i, u i) := by
  unfold Phi
  split_ifs with hy
  · have := shift_full hD u hu huj (w - ∑ i, u i) hy 0 le_rfl
    rw [zero_add, show w - ∑ i, u i + ∑ i, u i = w by ring] at this
    exact this
  · push_neg at hy
    have hey : (0 : Fin n → ℝ) ≤ (-(w - ∑ i, u i)) • Pi.single j (1 : ℝ) := sv_nonneg (by linarith) j
    have hej : ∀ i, i < j → ((-(w - ∑ i, u i)) • Pi.single j (1 : ℝ)) i = 0 := fun i hi => by
      simp [Pi.single_apply, hi.ne]
    have h1 := shift_full hD _ hey hej w hw u hu
    have h2 := shift_full hD u hu huj 0 le_rfl _ hey
    have hs : ∑ i, ((-(w - ∑ i, u i)) • Pi.single j (1 : ℝ)) i = -(w - ∑ i, u i) := by
      simp [Pi.single_apply]
    rw [hs] at h1
    rw [← h1, ← h2]
    congr 1
    · ring
    · exact add_comm _ _

/-! ### The stage step: `f_{s+1} - f'_{s+1}` is a function of the net level -/

theorem fstep (L L' : Levels.Model n) (s : ℕ) (j : Fin n)
    (ha : L.a (s + 1) = 1) (ha' : L'.a (s + 1) = 1) (hh : L'.h (s + 1) = L.h (s + 1))
    (hp : ∀ m, j ≤ m → L'.p (s + 1) m = L.p (s + 1) m)
    (hinv : Inv (fun z b => L.g s z b - L'.g s z b) j)
    (hmin : ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B → ∃ u ∈ Levels.feasible z B,
        ∀ u' ∈ Levels.feasible z B,
          L'.obj (s + 1) (L'.g s) z B u ≤ L'.obj (s + 1) (L'.g s) z B u') :
    ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B → (∀ i, i < j → B i = 0) →
      L.f (s + 1) z B = L'.f (s + 1) z B +
        Phi (fun z b => L.g s z b - L'.g s z b) j (z - ∑ i, B i) := by
  intro z hz B hB hBj
  have hobj : ∀ u ∈ Levels.feasible z B, L.obj (s + 1) (L.g s) z B u =
      L'.obj (s + 1) (L'.g s) z B u +
        Phi (fun z b => L.g s z b - L'.g s z b) j (z - ∑ i, B i) := by
    intro u hu
    obtain ⟨hu0, huB, hsum⟩ := hu
    have huj : ∀ i, i < j → u i = 0 := fun i hi => by
      have h1 : u i ≤ B i := huB i
      have h2 : (0 : ℝ) ≤ u i := hu0 i
      rw [hBj i hi] at h1
      exact le_antisymm h1 h2
    have hw : 0 ≤ z - ∑ i, (B i - u i) := by linarith
    have hdot : L.p (s + 1) ⬝ᵥ u = L'.p (s + 1) ⬝ᵥ u := by
      simp only [dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i < j
      · simp [huj i hi]
      · rw [hp i (not_lt.mp hi)]
    have hD := Phi_form hinv (z - ∑ i, (B i - u i)) hw u hu0 huj
    have hwu : z - ∑ i, (B i - u i) - ∑ i, u i = z - ∑ i, B i := by
      rw [Finset.sum_sub_distrib]; ring
    rw [hwu] at hD
    beta_reduce at hD
    simp only [Levels.Model.obj, ha, ha', one_smul, hh, hdot]
    linarith
  obtain ⟨u0, hu0F, hmin0⟩ := hmin z hz B hB
  have h1 : IsLeast (L'.obj (s + 1) (L'.g s) z B '' Levels.feasible z B)
      (L'.obj (s + 1) (L'.g s) z B u0) :=
    ⟨⟨u0, hu0F, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmin0 u hu⟩
  have h2 : IsLeast (L.obj (s + 1) (L.g s) z B '' Levels.feasible z B)
      (L'.obj (s + 1) (L'.g s) z B u0 +
        Phi (fun z b => L.g s z b - L'.g s z b) j (z - ∑ i, B i)) :=
    ⟨⟨u0, hu0F, hobj u0 hu0F⟩, by
      rintro _ ⟨u, hu, rfl⟩
      rw [hobj u hu]
      linarith [hmin0 u hu]⟩
  show sInf (L.obj (s + 1) (L.g s) z B '' Levels.feasible z B) =
    sInf (L'.obj (s + 1) (L'.g s) z B '' Levels.feasible z B) +
      Phi (fun z b => L.g s z b - L'.g s z b) j (z - ∑ i, B i)
  rw [h1.csInf_eq, h2.csInf_eq]

/-! ### The expectation step -/

/-- The increment of `f_{s+1}` along `(ε, ε δ_m)`. -/
noncomputable def dfun (L : Levels.Model n) (s : ℕ) (m : Fin n) (ε z : ℝ) (B : Fin n → ℝ) : ℝ :=
  L.f (s + 1) (z + ε) (B + ε • Pi.single m 1) - L.f (s + 1) z B

theorem g_diff (L : Levels.Model n) (s : ℕ) (m : Fin n) (ε z : ℝ) (hz : 0 ≤ z) (hε : 0 ≤ ε)
    (b : Fin n → ℝ) (hb : 0 ≤ b)
    (hint : ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b →
      Integrable (fun x => L.f (s + 1) z (b + x)) (L.μ (s + 1))) :
    L.g (s + 1) (z + ε) (b + ε • Pi.single m 1) - L.g (s + 1) z b =
      ∫ x, dfun L s m ε z (b + x) ∂(L.μ (s + 1)) := by
  have e1 : L.g (s + 1) (z + ε) (b + ε • Pi.single m 1) =
      ∫ x, L.f (s + 1) (z + ε) (b + ε • Pi.single m 1 + x) ∂(L.μ (s + 1)) := rfl
  have e2 : L.g (s + 1) z b = ∫ x, L.f (s + 1) z (b + x) ∂(L.μ (s + 1)) := rfl
  rw [e1, e2, ← integral_sub (hint _ (by linarith) _ (add_nonneg hb (sv_nonneg hε m)))
    (hint z hz b hb)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [dfun]
  rw [add_right_comm b]

theorem reduce_proj (X : Levels.Model n) (s : ℕ) (m : Fin n) (ε z : ℝ) (hε : 0 < ε)
    (hz : 0 ≤ z)
    (hc : ∀ ε : ℝ, 0 < ε → ∀ m : Fin n, ∀ z, 0 ≤ z → ∀ B B' : Fin n → ℝ, 0 ≤ B → 0 ≤ B' →
      (∀ i, m < i → B i = B' i) →
        X.f (s + 1) z B - X.f (s + 1) (z + ε) (B + ε • Pi.single m 1) =
          X.f (s + 1) z B' - X.f (s + 1) (z + ε) (B' + ε • Pi.single m 1))
    (b x : Fin n → ℝ) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    dfun X s m ε z (b + x) = dfun X s m ε z (proj m b + pos (proj m x)) := by
  have hv : proj m b + pos (proj m x) = proj m (b + x) := by
    funext i
    have hxi : (0 : ℝ) ≤ x i := hx i
    simp only [proj, pos, Pi.add_apply]
    split_ifs
    · rw [max_eq_left hxi]
    · simp
  rw [hv]
  have h := hc ε hε m z hz (b + x) (proj m (b + x)) (add_nonneg hb hx)
    (proj_nonneg (add_nonneg hb hx)) (fun i hi => by simp [proj, hi])
  simp only [dfun]
  linarith

theorem gstep (L L' : Levels.Model n) (s : ℕ) (j : Fin n)
    (hP : IsProbabilityMeasure (L.μ (s + 1))) (hP' : IsProbabilityMeasure (L'.μ (s + 1)))
    (hi : iIndepFun (fun m (x : Fin n → ℝ) => x m) (L.μ (s + 1)))
    (hi' : iIndepFun (fun m (x : Fin n → ℝ) => x m) (L'.μ (s + 1)))
    (hmarg : ∀ m, j < m →
      (L'.μ (s + 1)).map (fun x => x m) = (L.μ (s + 1)).map (fun x => x m))
    (hnn : ∀ᵐ x ∂(L.μ (s + 1)), 0 ≤ x) (hnn' : ∀ᵐ x ∂(L'.μ (s + 1)), 0 ≤ x)
    (hint : ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b →
      Integrable (fun x => L.f (s + 1) z (b + x)) (L.μ (s + 1)))
    (hint' : ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b →
      Integrable (fun x => L'.f (s + 1) z (b + x)) (L'.μ (s + 1)))
    (hcont : ContinuousOn (fun q : ℝ × (Fin n → ℝ) => L.f (s + 1) q.1 q.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)))
    (hc : ∀ ε : ℝ, 0 < ε → ∀ m : Fin n, ∀ z, 0 ≤ z → ∀ B B' : Fin n → ℝ, 0 ≤ B → 0 ≤ B' →
      (∀ i, m < i → B i = B' i) →
        L.f (s + 1) z B - L.f (s + 1) (z + ε) (B + ε • Pi.single m 1) =
          L.f (s + 1) z B' - L.f (s + 1) (z + ε) (B' + ε • Pi.single m 1))
    (hc' : ∀ ε : ℝ, 0 < ε → ∀ m : Fin n, ∀ z, 0 ≤ z → ∀ B B' : Fin n → ℝ, 0 ≤ B → 0 ≤ B' →
      (∀ i, m < i → B i = B' i) →
        L'.f (s + 1) z B - L'.f (s + 1) (z + ε) (B + ε • Pi.single m 1) =
          L'.f (s + 1) z B' - L'.f (s + 1) (z + ε) (B' + ε • Pi.single m 1))
    (Φ : ℝ → ℝ)
    (hF : ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B → (∀ i, i < j → B i = 0) →
      L.f (s + 1) z B = L'.f (s + 1) z B + Φ (z - ∑ i, B i)) :
    Inv (fun z b => L.g (s + 1) z b - L'.g (s + 1) z b) j := by
  haveI := hP
  haveI := hP'
  intro m hjm z hz b hb ε hε
  rcases eq_or_lt_of_le hε with h0 | hpos
  · subst h0; simp
  have hdL := g_diff L s m ε z hz hε b hb hint
  have hdL' := g_diff L' s m ε z hz hε b hb hint'
  have hB : ∀ B : Fin n → ℝ, 0 ≤ B → (∀ i, ¬ m < i → B i = 0) →
      dfun L s m ε z B = dfun L' s m ε z B := by
    intro B hB0 hBm
    have hBj : ∀ i, i < j → B i = 0 := fun i hi =>
      hBm i (fun h => lt_irrefl i ((hi.trans_le hjm).trans h))
    have hB2 : 0 ≤ B + ε • Pi.single m (1 : ℝ) := add_nonneg hB0 (sv_nonneg hpos.le m)
    have hB2j : ∀ i, i < j → (B + ε • Pi.single m (1 : ℝ) : Fin n → ℝ) i = 0 := fun i hi => by
      have him : i ≠ m := fun h => by subst h; exact absurd hjm (not_le.mpr hi)
      simp [hBj i hi, Pi.single_apply, him]
    have e1 := hF (z + ε) (by linarith) _ hB2 hB2j
    have e2 := hF z hz B hB0 hBj
    rw [sum_shift B m ε, show z + ε - (∑ i, B i + ε) = z - ∑ i, B i by ring] at e1
    simp only [dfun]
    rw [e1, e2]
    ring
  have hpos_c : Continuous (pos : (Fin n → ℝ) → (Fin n → ℝ)) :=
    continuous_pi fun i => (continuous_apply i).max continuous_const
  let H : (Fin n → ℝ) → ℝ := fun y => dfun L s m ε z (proj m b + pos y)
  have hH : Continuous H := by
    have c1 : Continuous (fun y : Fin n → ℝ =>
        L.f (s + 1) (z + ε) (proj m b + pos y + ε • Pi.single m (1 : ℝ))) := by
      have := hcont.comp_continuous
        (f := fun y : Fin n → ℝ => ((z + ε), proj m b + pos y + ε • Pi.single m (1 : ℝ)))
        (continuous_const.prodMk ((continuous_const.add hpos_c).add continuous_const))
        (fun y => Set.mk_mem_prod (Set.mem_Ici.mpr (by linarith))
          (Set.mem_Ici.mpr (add_nonneg (add_nonneg (proj_nonneg hb) (pos_nonneg y))
            (sv_nonneg hpos.le m))))
      exact this
    have c2 : Continuous (fun y : Fin n → ℝ => L.f (s + 1) z (proj m b + pos y)) := by
      have := hcont.comp_continuous
        (f := fun y : Fin n → ℝ => (z, proj m b + pos y))
        (continuous_const.prodMk (continuous_const.add hpos_c))
        (fun y => Set.mk_mem_prod (Set.mem_Ici.mpr hz)
          (Set.mem_Ici.mpr (add_nonneg (proj_nonneg hb) (pos_nonneg y))))
      exact this
    exact c1.sub c2
  have hLint : ∫ x, dfun L s m ε z (b + x) ∂(L.μ (s + 1)) =
      ∫ x, H (proj m x) ∂(L.μ (s + 1)) := by
    refine integral_congr_ae ?_
    filter_upwards [hnn] with x hx
    exact reduce_proj L s m ε z hpos hz hc b x hb hx
  have hL'int : ∫ x, dfun L' s m ε z (b + x) ∂(L'.μ (s + 1)) =
      ∫ x, H (proj m x) ∂(L'.μ (s + 1)) := by
    refine integral_congr_ae ?_
    filter_upwards [hnn'] with x hx
    rw [reduce_proj L' s m ε z hpos hz hc' b x hb hx]
    exact (hB _ (add_nonneg (proj_nonneg hb) (pos_nonneg _))
      (fun i hi => by simp [proj, pos, hi])).symm
  have hmap := map_proj_eq (L.μ (s + 1)) (L'.μ (s + 1)) hi hi' m
    (fun i hmi => hmarg i (lt_of_le_of_lt hjm hmi))
  have hI : ∫ x, H (proj m x) ∂(L.μ (s + 1)) = ∫ x, H (proj m x) ∂(L'.μ (s + 1)) := by
    rw [← integral_map (proj_measurable m).aemeasurable hH.aestronglyMeasurable,
      ← integral_map (proj_measurable m).aemeasurable hH.aestronglyMeasurable, hmap]
  show L.g (s + 1) (z + ε) (b + ε • Pi.single m 1) - L'.g (s + 1) (z + ε) (b + ε • Pi.single m 1) =
    L.g (s + 1) z b - L'.g (s + 1) z b
  linarith [hdL, hdL', hLint, hL'int, hI]

/-! ### Induction over the intervals -/

theorem inv_all (L L' : Levels.Model n) (hL : L.Standing) (hL' : L'.Standing) (t : ℕ)
    (htk : t ≤ L.k) (hk : L'.k = L.k)
    (ha : ∀ i ∈ Finset.Icc 1 t, L.a i = 1) (ha' : ∀ i ∈ Finset.Icc 1 t, L'.a i = 1)
    (hind : ∀ i ∈ Finset.Icc 1 L.k, iIndepFun (fun m (x : Fin n → ℝ) => x m) (L.μ i))
    (hind' : ∀ i ∈ Finset.Icc 1 L.k, iIndepFun (fun m (x : Fin n → ℝ) => x m) (L'.μ i))
    (j : Fin n) (hh : ∀ i ∈ Finset.Icc 1 t, L'.h i = L.h i) (hv₁ : L'.v₁ = L.v₁)
    (hv₂ : L'.v₂ = L.v₂)
    (hp : ∀ i ∈ Finset.Icc 1 t, ∀ m, j ≤ m → L'.p i m = L.p i m)
    (hd : ∀ i ∈ Finset.Icc 1 L.k, ∀ m, j < m →
      (L'.μ i).map (fun x => x m) = (L.μ i).map (fun x => x m)) :
    ∀ s, s ≤ t → Inv (fun z b => L.g s z b - L'.g s z b) j := by
  intro s
  induction s with
  | zero =>
    intro _ m _ z _ b _ ε _
    simp only [Levels.Model.g, hv₁, hv₂, sub_self]
  | succ s ih =>
    intro hs
    have hIH := ih (by omega)
    have hmem : s + 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨by omega, hs⟩
    have hmemk : s + 1 ∈ Finset.Icc 1 L.k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hmemk' : s + 1 ∈ Finset.Icc 1 L'.k := by rw [hk]; exact hmemk
    have hsk : s + 1 ≤ L.k := by omega
    have hsk' : s + 1 ≤ L'.k := by omega
    have l2 := Levels.lemma_2 L hL (s + 1) hsk
    have l2' := Levels.lemma_2 L' hL' (s + 1) hsk'
    have ha01 : ∀ i ∈ Finset.Icc 1 (s + 1), L.a i = 0 ∨ L.a i = 1 := fun i hi => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
      exact Or.inr (ha i (Finset.mem_Icc.mpr ⟨h1, by omega⟩))
    have ha01' : ∀ i ∈ Finset.Icc 1 (s + 1), L'.a i = 0 ∨ L'.a i = 1 := fun i hi => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
      exact Or.inr (ha' i (Finset.mem_Icc.mpr ⟨h1, by omega⟩))
    have T1 := Levels.theorem_1 L hL (s + 1) hmemk ha01
      (fun m => (Levels.criticalLevel_exists L hL (s + 1) hmemk m).exists.choose)
      (fun m => (Levels.criticalLevel_exists L hL (s + 1) hmemk m).exists.choose_spec)
    have T1' := Levels.theorem_1 L' hL' (s + 1) hmemk' ha01'
      (fun m => (Levels.criticalLevel_exists L' hL' (s + 1) hmemk' m).exists.choose)
      (fun m => (Levels.criticalLevel_exists L' hL' (s + 1) hmemk' m).exists.choose_spec)
    have hF := fstep L L' s j (ha _ hmem) (ha' _ hmem) (hh _ hmem) (hp _ hmem) hIH
      (fun z hz B hB => by
        obtain ⟨u, hu, -, hmin⟩ := l2'.2.2.1 (by omega) z hz B hB
        exact ⟨u, hu, hmin⟩)
    exact gstep L L' s j (hL.μ_prob _ hmemk) (hL'.μ_prob _ hmemk') (hind _ hmemk)
      (hind' _ hmemk) (hd _ hmemk) (hL.μ_nonneg _ hmemk) (hL'.μ_nonneg _ hmemk')
      (l2.2.2.2 (by omega)) (l2'.2.2.2 (by omega)) (l2.2.1 (by omega)).2
      (fun ε hε m z hz B B' hB hB' hBB => (T1.2.2 ε hε m z hz).1 B B' hB hB' hBB)
      (fun ε hε m z hz B B' hB hB' hBB => (T1'.2.2 ε hε m z hz).1 B B' hB hB' hBB) _ hF

/-! ### Uniqueness of the critical level up to an additive constant -/

theorem crit_unique (φ φ' : ℝ → ℝ) (c : ℝ) (h : ∀ w, 0 ≤ w → φ w = φ' w + c)
    (z₁ z₁' : WithTop ℝ) (h1 : Levels.IsCriticalLevel φ z₁)
    (h2 : Levels.IsCriticalLevel φ' z₁') : z₁ = z₁' := by
  rcases h1 with ⟨rfl, hA⟩ | ⟨x, rfl, hx0, hxmin, hxsmall⟩ <;>
    rcases h2 with ⟨rfl, hA'⟩ | ⟨x', rfl, hx0', hxmin', hxsmall'⟩
  · rfl
  · exfalso
    have k1 := hA (Set.mem_Ici.mpr hx0') (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ x' + 1))
      (by linarith : x' < x' + 1)
    have k2 := hxmin' (x' + 1) (by linarith)
    have k3 := h x' hx0'
    have k4 := h (x' + 1) (by linarith)
    linarith
  · exfalso
    have k1 := hA' (Set.mem_Ici.mpr hx0) (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ x + 1))
      (by linarith : x < x + 1)
    have k2 := hxmin (x + 1) (by linarith)
    have k3 := h x hx0
    have k4 := h (x + 1) (by linarith)
    linarith
  · have le1 : x ≤ x' := hxsmall x' hx0' (fun w hw => by
      have := hxmin' w hw
      rw [h x' hx0', h w hw]; linarith)
    have le2 : x' ≤ x := hxsmall' x hx0 (fun w hw => by
      have := hxmin w hw
      have k3 := h x hx0
      have k4 := h w hw
      linarith)
    rw [le_antisymm le1 le2]

end T3Aux

open TopkisRation.Backlog MeasureTheory ProbabilityTheory in
theorem solution {n : ℕ} (M M' : Model n) (hM : M.Standing) (hM' : M'.Standing)
    (t : ℕ) (htk : t + 1 ≤ M.k) (hk : M'.k = M.k)
    (ha : ∀ i ∈ Finset.Icc 1 (t + 1), M.a i = 1) (ha' : ∀ i ∈ Finset.Icc 1 (t + 1), M'.a i = 1)
    (hind : ∀ i ∈ Finset.Icc 1 M.k, iIndepFun (fun m (x : Fin n → ℝ) => x m) (M.μ i))
    (hind' : ∀ i ∈ Finset.Icc 1 M.k, iIndepFun (fun m (x : Fin n → ℝ) => x m) (M'.μ i))
    (j : Fin n)
    (hh : ∀ i ∈ Finset.Icc 1 (t + 1), M'.h i = M.h i) (hv₁ : M'.v₁ = M.v₁) (hv₂ : M'.v₂ = M.v₂)
    (hp : ∀ i ∈ Finset.Icc 1 (t + 1), ∀ m, j ≤ m → M'.p i m = M.p i m)
    (hd : ∀ i ∈ Finset.Icc 1 M.k, ∀ m, j < m →
      (M'.μ i).map (fun x => x m) = (M.μ i).map (fun x => x m)) :
    (∀ z, 0 ≤ z →
      TopkisRation.Levels.rightDeriv (fun z => M.g t z (z • Pi.single j 1)) z =
        TopkisRation.Levels.rightDeriv (fun z => M'.g t z (z • Pi.single j 1)) z) ∧
    (∀ s : Fin n, j < s → ∀ w, 0 ≤ w → ∀ b : Fin n → ℝ, 0 ≤ b → 0 < b s →
      TopkisRation.Levels.rightDeriv (fun ε => M.g t w (ε • (Pi.single j 1 - Pi.single s 1) + b)) 0 =
        TopkisRation.Levels.rightDeriv (fun ε => M'.g t w (ε • (Pi.single j 1 - Pi.single s 1) + b)) 0) ∧
    (∀ z₁ z₁' : WithTop ℝ, TopkisRation.Levels.IsCriticalLevel (M.levelObj (t + 1) j) z₁ →
      TopkisRation.Levels.IsCriticalLevel (M'.levelObj (t + 1) j) z₁' → z₁ = z₁') := by
  have icc : ∀ i, i ∈ Finset.Icc 1 t → i ∈ Finset.Icc 1 (t + 1) := fun i hi => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
  have hmemt : t + 1 ∈ Finset.Icc 1 (t + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hinv := T3Aux.inv_all (T3Aux.toL M) (T3Aux.toL M') (T3Aux.standing M hM)
    (T3Aux.standing M' hM') t (show t ≤ M.k by omega) hk (fun i hi => ha i (icc i hi))
    (fun i hi => ha' i (icc i hi)) hind hind' j (fun i hi => hh i (icc i hi)) hv₁ hv₂
    (fun i hi => hp i (icc i hi)) hd t le_rfl
  have key : ∀ m : Fin n, j ≤ m → ∀ z : ℝ, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b → ∀ ε : ℝ, 0 ≤ ε →
      M.g t (z + ε) (b + ε • Pi.single m 1) - M.g t z b =
        M'.g t (z + ε) (b + ε • Pi.single m 1) - M'.g t z b := by
    intro m hm z hz b hb ε hε
    have := hinv m hm z hz b hb ε hε
    beta_reduce at this
    rw [← T3Aux.g_eq M t, ← T3Aux.g_eq M' t] at this
    linarith
  refine ⟨fun z hz => ?_, fun s hjs w hw b hb hbs => ?_, fun z₁ z₁' h1 h2 => ?_⟩
  · unfold TopkisRation.Levels.rightDeriv
    apply Filter.liminf_congr
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have hzd : (z + ε) • Pi.single j (1 : ℝ) = z • Pi.single j 1 + ε • Pi.single j 1 :=
      add_smul _ _ _
    have h2 : M.g t (z + ε) ((z + ε) • Pi.single j 1) - M.g t z (z • Pi.single j 1) =
        M'.g t (z + ε) ((z + ε) • Pi.single j 1) - M'.g t z (z • Pi.single j 1) := by
      rw [hzd]
      exact key j le_rfl z hz (z • Pi.single j 1) (T3Aux.sv_nonneg hz j) ε hε'.le
    rw [h2]
  · unfold TopkisRation.Levels.rightDeriv
    apply Filter.liminf_congr
    filter_upwards [Ioo_mem_nhdsGT hbs] with ε hε
    obtain ⟨hε0, hεb⟩ := hε
    have hjs' : s ≠ j := (ne_of_lt hjs).symm
    have hv : (0 : Fin n → ℝ) ≤ ε • (Pi.single j (1 : ℝ) - Pi.single s 1) + b := by
      intro i
      have hbi : (0 : ℝ) ≤ b i := hb i
      show (0 : ℝ) ≤ (ε • (Pi.single j (1 : ℝ) - Pi.single s 1) + b : Fin n → ℝ) i
      by_cases hij : i = j
      · subst hij
        simp [Pi.single_apply, hjs'.symm]
        linarith
      · by_cases his : i = s
        · subst his
          simp [Pi.single_apply, hij]
          linarith
        · simp [Pi.single_apply, hij, his]
          exact hbi
    have hvs : ε • (Pi.single j (1 : ℝ) - Pi.single s 1) + b + ε • Pi.single s 1 =
        b + ε • Pi.single j 1 := by
      rw [smul_sub]; abel
    have k1 := key j le_rfl w hw b hb ε hε0.le
    have k2 := key s hjs.le w hw _ hv ε hε0.le
    rw [hvs] at k2
    have h2 : M.g t w (ε • (Pi.single j (1 : ℝ) - Pi.single s 1) + b) - M.g t w b =
        M'.g t w (ε • (Pi.single j (1 : ℝ) - Pi.single s 1) + b) - M'.g t w b := by
      linarith
    simp only [zero_add, zero_smul]
    rw [h2]
  · have hlev : ∀ w, 0 ≤ w → M.levelObj (t + 1) j w =
        M'.levelObj (t + 1) j w + (M.g t 0 0 - M'.g t 0 0) := by
      intro w hw
      have := key j le_rfl 0 le_rfl 0 le_rfl w hw
      simp only [zero_add] at this
      simp only [Model.levelObj, Nat.add_sub_cancel, ha (t + 1) hmemt, ha' (t + 1) hmemt,
        one_smul, hp (t + 1) hmemt j le_rfl, hh (t + 1) hmemt]
      linarith
    exact T3Aux.crit_unique _ _ _ hlev z₁ z₁' h1 h2
