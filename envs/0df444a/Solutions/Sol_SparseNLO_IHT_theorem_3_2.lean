-- Prove2me | solution 1 for SparseNLO.IHT.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T19:38:52.502668+00:00
-- url     : https://prove2.me/submissions/21be8e9f-5e99-444e-9157-908cdfe2d15c

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

set_option autoImplicit false

open Filter Topology

namespace P3425f13e

open SparseNLO.IHT

variable {m n : ℕ}

noncomputable abbrev Tc (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

lemma Tc_apply (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Tc A x = Matrix.toEuclideanLin A x := rfl

lemma fLI_eq (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    fLI A b = fun x => ‖Tc A x - b‖ ^ 2 := rfl

lemma grad_fLI (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fLI A b) x = (2:ℝ) • (ContinuousLinearMap.adjoint (Tc A)) (Tc A x - b) := by
  have h : HasFDerivAt (fun x => ‖Tc A x - b‖ ^ 2)
      (2 • (innerSL ℝ (Tc A x - b)).comp (Tc A)) x :=
    ((Tc A).hasFDerivAt.sub_const b).norm_sq
  have e : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
      ((2:ℝ) • (ContinuousLinearMap.adjoint (Tc A)) (Tc A x - b)) =
      (2 • (innerSL ℝ (Tc A x - b)).comp (Tc A)) := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left, inner_smul_left,
      real_inner_comm]
  have h2 : HasGradientAt (fLI A b)
      ((2:ℝ) • (ContinuousLinearMap.adjoint (Tc A)) (Tc A x - b)) x := by
    rw [hasGradientAt_iff_hasFDerivAt, fLI_eq, e]
    exact h
  exact h2.gradient

lemma expand (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (x y : EuclideanSpace ℝ (Fin n)) :
    fLI A b y = fLI A b x + inner ℝ (gradient (fLI A b) x) (y - x) + ‖Tc A (y - x)‖ ^ 2 := by
  rw [grad_fLI, fLI_eq]
  simp only
  have : Tc A y - b = (Tc A x - b) + Tc A (y - x) := by simp
  rw [this, norm_add_sq_real, inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  simp

lemma quad_bound (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (Lf : NNReal) (hLip : LipschitzWith Lf (gradient (fLI A b)))
    (d : EuclideanSpace ℝ (Fin n)) : 2 * ‖Tc A d‖ ^ 2 ≤ (Lf : ℝ) * ‖d‖ ^ 2 := by
  have h := hLip.dist_le_mul d 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero, grad_fLI, grad_fLI] at h
  have e : (2:ℝ) • (ContinuousLinearMap.adjoint (Tc A)) (Tc A d - b) -
      (2:ℝ) • (ContinuousLinearMap.adjoint (Tc A)) (Tc A 0 - b) =
      (2:ℝ) • (ContinuousLinearMap.adjoint (Tc A)) (Tc A d) := by
    rw [← smul_sub, ← map_sub]; simp
  rw [e, norm_smul] at h
  have h3 : ‖Tc A d‖ ^ 2 ≤ ‖(ContinuousLinearMap.adjoint (Tc A)) (Tc A d)‖ * ‖d‖ := by
    have : inner ℝ (Tc A d) (Tc A d) = inner ℝ ((ContinuousLinearMap.adjoint (Tc A)) (Tc A d)) d := by
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [real_inner_self_eq_norm_sq] at this
    rw [this]
    exact real_inner_le_norm _ _
  have h4 : (2:ℝ) * ‖(ContinuousLinearMap.adjoint (Tc A)) (Tc A d)‖ ≤ Lf * ‖d‖ := by
    simpa using h
  nlinarith [norm_nonneg d]


lemma sep_exists {E : Type*} [MetricSpace E] (S : Set E) (hS : S.Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ dist p q := by
  classical
  set F : Finset (E × E) := (hS.toFinset ×ˢ hS.toFinset).filter (fun pq => pq.1 ≠ pq.2) with hF
  by_cases h : F.Nonempty
  · refine ⟨F.inf' h (fun pq => dist pq.1 pq.2), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro pq hpq
      simp only [hF, Finset.mem_filter] at hpq
      exact dist_pos.2 hpq.2
    · intro p hp q hq hpq
      have hm : (p, q) ∈ F := by simp [hF, hpq, hp, hq]
      exact Finset.inf'_le (fun pq : E × E => dist pq.1 pq.2) hm
  · refine ⟨1, one_pos, ?_⟩
    intro p hp q hq hpq
    exfalso; apply h
    exact ⟨(p, q), by simp [hF, hpq, hp, hq]⟩

lemma conv_finite {E : Type*} [MetricSpace E] [ProperSpace E] (S : Set E) (hS : S.Finite)
    (x : ℕ → E) (hb : Bornology.IsBounded (Set.range x))
    (hstep : Tendsto (fun k => dist (x (k + 1)) (x k)) atTop (𝓝 0))
    (hcl : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ c, Tendsto (fun j => x (φ j)) atTop (𝓝 c) → c ∈ S) :
    ∃ p, Tendsto x atTop (𝓝 p) := by
  obtain ⟨δ, hδ, hsep⟩ := sep_exists S hS
  -- step 1: eventually close to S
  have h1 : ∀ᶠ k in atTop, ∃ p ∈ S, dist (x k) p < δ / 4 := by
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hcon
    obtain ⟨c, -, ψ, hψ, hψc⟩ := tendsto_subseq_of_bounded hb (x := fun j => x (φ j))
      (fun j => ⟨φ j, rfl⟩)
    have hφψ : Tendsto (φ ∘ ψ) atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
    have hcS : c ∈ S := hcl (φ ∘ ψ) hφψ c hψc
    have := hφP (ψ 0)
    have hcont : Tendsto (fun j => dist (x (φ (ψ j))) c) atTop (𝓝 0) := by
      simpa using (tendsto_iff_dist_tendsto_zero.1 hψc)
    have hge : ∀ j, δ / 4 ≤ dist (x (φ (ψ j))) c := by
      intro j
      have := hφP (ψ j)
      push Not at this
      exact this c hcS
    have := ge_of_tendsto hcont (Filter.Eventually.of_forall hge)
    linarith
  have h2 : ∀ᶠ k in atTop, dist (x (k + 1)) (x k) < δ / 4 :=
    hstep.eventually (gt_mem_nhds (by linarith))
  obtain ⟨K, hK⟩ := (h1.and h2).exists_forall_of_atTop
  obtain ⟨p, hpS, hp0⟩ := (hK K le_rfl).1
  have hall : ∀ k, K ≤ k → dist (x k) p < δ / 4 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hp0
    | succ k hk ih =>
      obtain ⟨q, hqS, hq⟩ := (hK (k + 1) (by omega)).1
      have hs := (hK k hk).2
      have hpq : dist p q < δ := by
        have h1 := dist_triangle p (x k) q
        have h2 := dist_triangle (x k) (x (k + 1)) q
        have h3 := dist_comm (x k) (x (k + 1))
        have h4 := dist_comm p (x k)
        linarith
      by_cases hEq : p = q
      · subst hEq; exact hq
      · exact absurd (hsep p hpS q hqS hEq) (not_le.2 hpq)
  refine ⟨p, tendsto_of_subseq_tendsto ?_⟩
  intro ns hns
  obtain ⟨c, -, ψ, hψ, hψc⟩ := tendsto_subseq_of_bounded hb (x := fun j => x (ns j))
    (fun j => ⟨ns j, rfl⟩)
  have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
  have hcS : c ∈ S := hcl (ns ∘ ψ) hnsψ c hψc
  have hcp : dist c p ≤ δ / 4 := by
    have hcont : Tendsto (fun j => dist (x (ns (ψ j))) p) atTop (𝓝 (dist c p)) :=
      (hψc.dist tendsto_const_nhds)
    refine le_of_tendsto hcont ?_
    have : ∀ᶠ j in atTop, K ≤ ns (ψ j) := hnsψ.eventually (eventually_ge_atTop K)
    filter_upwards [this] with j hj
    exact (hall _ hj).le
  have : c = p := by
    by_contra hne
    have := hsep c hcS p hpS hne
    linarith
  subst this
  exact ⟨ψ, hψc⟩


open SparseNLO.CWOpt in
lemma mem_Cs_of_sub (s : ℕ) (I : Finset (Fin n)) (hI : I.card ≤ s)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, i ∉ I → x i = 0) : x ∈ Cs n s := by
  show l0 x ≤ s
  unfold l0
  refine le_trans (Finset.card_le_card ?_) hI
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra h
  exact hi (hx i h)

open SparseNLO.CWOpt in
lemma exists_I (s : ℕ) (hsn : s ≤ n) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Cs n s) :
    ∃ I : Finset (Fin n), I.card = s ∧ ∀ i, i ∉ I → x i = 0 := by
  have hx' : (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ s := hx
  obtain ⟨I, hI, hIc⟩ := Finset.exists_superset_card_eq hx' (by simpa using hsn)
  refine ⟨I, hIc, fun i hi => ?_⟩
  by_contra h
  exact hi (hI (by simp [h]))

open SparseNLO.CWOpt in
lemma Cs_closed (s : ℕ) (hsn : s ≤ n) : IsClosed (Cs n s : Set (EuclideanSpace ℝ (Fin n))) := by
  have : (Cs n s : Set (EuclideanSpace ℝ (Fin n))) =
      ⋃ I ∈ (Finset.univ.filter (fun I : Finset (Fin n) => I.card = s)),
        {x | ∀ i, i ∉ I → x i = 0} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · intro hx
      obtain ⟨I, h1, h2⟩ := exists_I s hsn hx
      exact ⟨I, h1, h2⟩
    · rintro ⟨I, h1, h2⟩
      exact mem_Cs_of_sub s I h1.le h2
  rw [this]
  refine isClosed_biUnion_finset (fun I _ => ?_)
  have : {x : EuclideanSpace ℝ (Fin n) | ∀ i, i ∉ I → x i = 0} =
      ⋂ i ∈ (Iᶜ : Finset (Fin n)), {x | x i = 0} := by
    ext x; simp
  rw [this]
  refine isClosed_biInter (fun i _ => ?_)
  exact isClosed_eq (EuclideanSpace.proj i).continuous continuous_const

lemma Tc_apply_coord (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n)) (r : Fin m) :
    (Tc A d) r = ∑ i, A r i * d i := by
  simp [Tc_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

lemma inj_on_I (s : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (hA : IsSRegular s A)
    (I : Finset (Fin n)) (hI : I.card = s) (d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ i, i ∉ I → d i = 0) (h0 : Tc A d = 0) : d = 0 := by
  have hli := hA I hI
  rw [Fintype.linearIndependent_iff] at hli
  have hsum : ∑ i : (I : Set (Fin n)), d i • (fun r : Fin m => A r i) = 0 := by
    funext r
    have := congrArg (fun v => v r) h0
    simp only [Tc_apply_coord, PiLp.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e : ∑ i : (I : Set (Fin n)), d i * A r i = ∑ i ∈ I, d i * A r i :=
      Finset.sum_coe_sort I (fun i => d i * A r i)
    rw [e, ← this]
    rw [← Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by rw [hd i hi]; ring)]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have := hli (fun i => d i) hsum
  ext i
  by_cases hi : i ∈ I
  · exact this ⟨i, hi⟩
  · exact hd i hi


open SparseNLO.CWOpt in
lemma coercive (s : ℕ) (hsn : s ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (hA : IsSRegular s A) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Cs n s, c * ‖x‖ ≤ ‖Tc A x‖ := by
  have hCs := Cs_closed (n := n) s hsn
  have hK : IsCompact ((Cs n s : Set (EuclideanSpace ℝ (Fin n))) ∩
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (isCompact_sphere 0 1).inter_left hCs
  have hscale : ∀ x ∈ (Cs n s : Set (EuclideanSpace ℝ (Fin n))), x ≠ 0 →
      ‖x‖⁻¹ • x ∈ (Cs n s : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.sphere 0 1 := by
    intro x hx hx0
    refine ⟨?_, ?_⟩
    · obtain ⟨I, h1, h2⟩ := exists_I s hsn hx
      exact mem_Cs_of_sub s I h1.le (fun i hi => by simp [h2 i hi])
    · simp [norm_smul, hx0]
  rcases Set.eq_empty_or_nonempty ((Cs n s : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with he | hne
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    by_cases hx0 : x = 0
    · simp [hx0]
    · have := hscale x hx hx0
      rw [he] at this
      exact absurd this (Set.notMem_empty _)
  · obtain ⟨x0, hx0K, hmin⟩ := hK.exists_isMinOn hne (f := fun y => ‖Tc A y‖) (by fun_prop)
    have hx0norm : ‖x0‖ = 1 := by simpa using hx0K.2
    have hx0ne : x0 ≠ 0 := by
      intro h; rw [h] at hx0norm; simp at hx0norm
    have hpos : 0 < ‖Tc A x0‖ := by
      rw [norm_pos_iff]
      intro h0
      obtain ⟨I, h1, h2⟩ := exists_I s hsn hx0K.1
      exact hx0ne (inj_on_I s A hA I h1 x0 h2 h0)
    refine ⟨‖Tc A x0‖, hpos, fun x hx => ?_⟩
    by_cases hx0' : x = 0
    · simp [hx0']
    · have hy := hscale x hx hx0'
      have h1 := hmin hy
      simp only [Set.mem_setOf_eq] at h1
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0'
      rw [map_smul, norm_smul, norm_inv, norm_norm] at h1
      have : ‖Tc A x0‖ * ‖x‖ ≤ ‖x‖⁻¹ * ‖Tc A x‖ * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right h1 hxpos.le
      rw [mul_assoc, mul_comm (‖Tc A x‖) ‖x‖, ← mul_assoc, inv_mul_cancel₀ hxpos.ne', one_mul] at this
      linarith

open SparseNLO.CWOpt in
lemma run_mem (s : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsIHTRun f s L x) : ∀ k, x k ∈ Cs n s := by
  intro k
  cases k with
  | zero => exact hx.1
  | succ k => exact (hx.2 k).1

lemma descent (s : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (Lf : NNReal) (hLip : LipschitzWith Lf (gradient (fLI A b))) (L : ℝ) (hL : (Lf : ℝ) < L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsIHTRun (fLI A b) s L x) (k : ℕ) :
    fLI A b (x (k + 1)) ≤ fLI A b (x k) - (L - Lf) / 2 * ‖x (k + 1) - x k‖ ^ 2 := by
  have hLpos : 0 < L := lt_of_le_of_lt Lf.coe_nonneg hL
  obtain ⟨-, hmin⟩ := hx.2 k
  have hle := hmin (x k) (run_mem s _ L x hx k)
  set g := gradient (fLI A b) (x k) with hg
  set d := x (k + 1) - x k with hd
  have e1 : x (k + 1) - (x k - (1 / L) • g) = d + (1 / L) • g := by
    simp [hd]; abel
  have e2 : x k - (x k - (1 / L) • g) = (1 / L) • g := by simp
  rw [e1, e2] at hle
  have hsq : ‖d + (1 / L) • g‖ ^ 2 ≤ ‖(1 / L) • g‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [norm_add_sq_real, inner_smul_right] at hsq
  have hinner : inner ℝ g d ≤ -(L / 2) * ‖d‖ ^ 2 := by
    rw [real_inner_comm] at hsq
    have h1 : ‖d‖ ^ 2 + 2 * (1 / L) * inner ℝ g d ≤ 0 := by linarith
    have h2 : 2 * (1 / L) * inner ℝ g d ≤ - ‖d‖ ^ 2 := by linarith
    have h3 : inner ℝ g d ≤ -‖d‖ ^ 2 * L / 2 := by
      have := mul_le_mul_of_nonneg_left h2 hLpos.le
      field_simp at this
      linarith
    linarith
  have hexp := expand A b (x k) (x (k + 1))
  have hq := quad_bound A b Lf hLip d
  rw [← hd] at hexp
  rw [← hg] at hexp
  nlinarith


lemma stat_data (s : ℕ) (hsn : s ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 < L)
    (p : EuclideanSpace ℝ (Fin n)) (hp : IsLStationary f s L p) :
    ∃ I : Finset (Fin n), I.card = s ∧ (∀ i, i ∉ I → p i = 0) ∧ ∀ i ∈ I, gradient f p i = 0 := by
  obtain ⟨hpC, -, hmin⟩ := hp
  obtain ⟨I, hIc, hI⟩ := exists_I s hsn hpC
  refine ⟨I, hIc, hI, fun i hi => ?_⟩
  set g := gradient f p with hg
  set t : ℝ := -(1 / L) * g i with ht
  have hz : p + EuclideanSpace.single i t ∈ SparseNLO.CWOpt.Cs n s := by
    refine mem_Cs_of_sub s I hIc.le (fun j hj => ?_)
    have hji : j ≠ i := fun h => hj (h ▸ hi)
    simp [hI j hj, EuclideanSpace.single_apply, hji]
  have hle := hmin _ hz
  have e1 : p - (p - (1 / L) • g) = (1 / L) • g := by simp
  have e2 : p + EuclideanSpace.single i t - (p - (1 / L) • g) =
      (1 / L) • g + EuclideanSpace.single i t := by abel
  rw [e1, e2] at hle
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [norm_add_sq_real, EuclideanSpace.inner_single_right, EuclideanSpace.norm_single] at hsq
  simp only [PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs, conj_trivial] at hsq
  have : (1 / L * g i) ^ 2 ≤ 0 := by
    have h2 : t * (1 / L * g i) = -(1 / L * g i) ^ 2 := by rw [ht]; ring
    have h3 : t ^ 2 = (1 / L * g i) ^ 2 := by rw [ht]; ring
    nlinarith
  have h0 : 1 / L * g i = 0 := by nlinarith [sq_nonneg (1 / L * g i)]
  have : g i = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (by positivity)
    · exact h
  exact this

lemma stat_unique (s : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (hA : IsSRegular s A) (I : Finset (Fin n)) (hI : I.card = s)
    (p q : EuclideanSpace ℝ (Fin n))
    (hp0 : ∀ i, i ∉ I → p i = 0) (hq0 : ∀ i, i ∉ I → q i = 0)
    (hpg : ∀ i ∈ I, gradient (fLI A b) p i = 0) (hqg : ∀ i ∈ I, gradient (fLI A b) q i = 0) :
    p = q := by
  set d := p - q with hd
  have hd0 : ∀ i, i ∉ I → d i = 0 := fun i hi => by simp [hd, hp0 i hi, hq0 i hi]
  have hadj : ∀ i ∈ I, ((ContinuousLinearMap.adjoint (Tc A)) (Tc A d)) i = 0 := by
    intro i hi
    have h1 := hpg i hi
    have h2 := hqg i hi
    rw [grad_fLI] at h1 h2
    have e : (ContinuousLinearMap.adjoint (Tc A)) (Tc A d) =
        (ContinuousLinearMap.adjoint (Tc A)) (Tc A p - b) - (ContinuousLinearMap.adjoint (Tc A)) (Tc A q - b) := by
      rw [← map_sub]; congr 1; simp [hd]
    rw [e]
    simp only [PiLp.smul_apply, smul_eq_mul, mul_eq_zero] at h1 h2
    simp only [PiLp.sub_apply]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · norm_num at h1
    · norm_num at h1
    · norm_num at h2
    · rw [h1, h2]; ring
  have hnorm : ‖Tc A d‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hi : i ∈ I
    · rw [hadj i hi]; simp
    · simp [hd0 i hi]
  have hT : Tc A d = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 hnorm
    exact norm_eq_zero.1 this
  exact sub_eq_zero.1 (inj_on_I s A hA I hI d hd0 hT)


lemma stat_finite (s : ℕ) (hsn : s ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (hA : IsSRegular s A) (L : ℝ) (hL : 0 < L) :
    {p : EuclideanSpace ℝ (Fin n) | IsLStationary (fLI A b) s L p}.Finite := by
  classical
  have hsub : {p : EuclideanSpace ℝ (Fin n) | IsLStationary (fLI A b) s L p} ⊆
      ⋃ I ∈ (Finset.univ.filter (fun I : Finset (Fin n) => I.card = s)),
        {p | (∀ i, i ∉ I → p i = 0) ∧ ∀ i ∈ I, gradient (fLI A b) p i = 0} := by
    intro p hp
    obtain ⟨I, h1, h2, h3⟩ := stat_data s hsn _ L hL p hp
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      exists_prop]
    exact ⟨I, h1, h2, h3⟩
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun I hI => ?_)
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hI
  apply Set.Subsingleton.finite
  intro p hp q hq
  exact stat_unique s A b hA I hI p q hp.1 hq.1 hp.2 hq.2

lemma cluster_stat (s : ℕ) (hsn : s ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (Lf : NNReal) (hLip : LipschitzWith Lf (gradient (fLI A b))) (L : ℝ) (hL : 0 < L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsIHTRun (fLI A b) s L x)
    (hstep : Tendsto (fun k => dist (x (k + 1)) (x k)) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (c : EuclideanSpace ℝ (Fin n))
    (hc : Tendsto (fun j => x (φ j)) atTop (𝓝 c)) : IsLStationary (fLI A b) s L c := by
  have hCs := Cs_closed (n := n) s hsn
  have hcC : c ∈ SparseNLO.CWOpt.Cs n s :=
    hCs.mem_of_tendsto hc (Filter.Eventually.of_forall (fun j => run_mem s _ L x hx (φ j)))
  have hc1 : Tendsto (fun j => x (φ j + 1)) atTop (𝓝 c) := by
    refine hc.congr_dist ?_
    have := hstep.comp hφ
    simpa [Function.comp_def, dist_comm] using this
  have hg : Continuous (gradient (fLI A b)) := hLip.continuous
  have hy : Tendsto (fun j => x (φ j) - (1 / L) • gradient (fLI A b) (x (φ j))) atTop
      (𝓝 (c - (1 / L) • gradient (fLI A b) c)) :=
    hc.sub (((hg.tendsto c).comp hc).const_smul (1 / L))
  refine ⟨hcC, hcC, fun z hz => ?_⟩
  have hlim1 := (hc1.sub hy).norm
  have hlim2 := (tendsto_const_nhds (x := z)).sub hy |>.norm
  refine le_of_tendsto_of_tendsto' hlim1 hlim2 (fun j => ?_)
  exact (hx.2 (φ j)).2 z hz


lemma main {s : ℕ} (hsn : s ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (hA : IsSRegular s A) (Lf : NNReal) (hLip : LipschitzWith Lf (gradient (fLI A b))) (L : ℝ)
    (hL : (Lf : ℝ) < L) (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsIHTRun (fLI A b) s L x) :
    ∃ xstar : EuclideanSpace ℝ (Fin n),
      IsLStationary (fLI A b) s L xstar ∧ Tendsto x atTop (𝓝 xstar) := by
  have hLpos : 0 < L := lt_of_le_of_lt Lf.coe_nonneg hL
  have hdesc := descent s A b Lf hLip L hL x hx
  have hf0 : ∀ y, 0 ≤ fLI A b y := fun y => by rw [fLI_eq]; positivity
  set a : ℕ → ℝ := fun k => fLI A b (x k) with ha
  set c : ℝ := (L - Lf) / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hdesc' : ∀ k, c * ‖x (k + 1) - x k‖ ^ 2 ≤ a k - a (k + 1) := fun k => by
    have := hdesc k; simp only [ha]; linarith
  have hsum : ∀ N, ∑ k ∈ Finset.range N, c * ‖x (k + 1) - x k‖ ^ 2 ≤ a 0 - a N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ]; have := hdesc' N; linarith
  have hmono : ∀ k, a k ≤ a 0 := by
    intro k
    have := hsum k
    have h2 : 0 ≤ ∑ j ∈ Finset.range k, c * ‖x (j + 1) - x j‖ ^ 2 :=
      Finset.sum_nonneg (fun j _ => by positivity)
    linarith
  have hsumm : Summable (fun k => c * ‖x (k + 1) - x k‖ ^ 2) :=
    summable_of_sum_range_le (c := a 0) (fun k => by positivity)
      (fun N => by have := hsum N; have := hf0 (x N); simp only [ha] at *; linarith)
  have hlim : Tendsto (fun k => ‖x (k + 1) - x k‖ ^ 2) atTop (𝓝 0) := by
    have h := hsumm.tendsto_atTop_zero
    have h2 := h.const_mul c⁻¹
    simp only [mul_zero] at h2
    refine h2.congr (fun k => ?_)
    field_simp
  have hstep : Tendsto (fun k => dist (x (k + 1)) (x k)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim
    simp only [Real.sqrt_zero] at h
    refine h.congr (fun k => ?_)
    simp [Function.comp_def, dist_eq_norm, Real.sqrt_sq (norm_nonneg _)]
  -- boundedness
  obtain ⟨c0, hc0, hcoer⟩ := coercive s hsn A hA
  have hbd : Bornology.IsBounded (Set.range x) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(‖b‖ + a 0 + 1) / c0, ?_⟩
    rintro _ ⟨k, rfl⟩
    have h1 := hcoer (x k) (run_mem s _ L x hx k)
    have h2 : ‖Tc A (x k)‖ ≤ ‖Tc A (x k) - b‖ + ‖b‖ := by
      have := norm_sub_le (Tc A (x k)) b
      have := norm_add_le (Tc A (x k) - b) b
      simpa using this
    have h3 : ‖Tc A (x k) - b‖ ^ 2 ≤ a 0 := by
      have := hmono k
      simpa [ha, fLI_eq] using this
    have h4 : ‖Tc A (x k) - b‖ ≤ ‖Tc A (x k) - b‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg (‖Tc A (x k) - b‖ - 1)]
    rw [le_div_iff₀ hc0]
    nlinarith
  have hfin := stat_finite s hsn A b hA L hLpos
  have hcl : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ c, Tendsto (fun j => x (φ j)) atTop (𝓝 c) →
      c ∈ {p : EuclideanSpace ℝ (Fin n) | IsLStationary (fLI A b) s L p} :=
    fun φ hφ c hc => cluster_stat s hsn A b Lf hLip L hLpos x hx hstep φ hφ c hc
  obtain ⟨p, hp⟩ := conv_finite _ hfin x hbd hstep hcl
  exact ⟨p, cluster_stat s hsn A b Lf hLip L hLpos x hx hstep (fun j => j) tendsto_id p hp, hp⟩

end P3425f13e

open Filter Topology SparseNLO.IHT in
theorem solution {m n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) (hA : IsSRegular s A)
    (Lf : NNReal) (hLip : LipschitzWith Lf (gradient (fLI A b))) (L : ℝ) (hL : (Lf : ℝ) < L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsIHTRun (fLI A b) s L x) :
    ∃ xstar : EuclideanSpace ℝ (Fin n),
      IsLStationary (fLI A b) s L xstar ∧ Tendsto x atTop (𝓝 xstar) := by
  exact P3425f13e.main hsn.le A b hA Lf hLip L hL x hx
