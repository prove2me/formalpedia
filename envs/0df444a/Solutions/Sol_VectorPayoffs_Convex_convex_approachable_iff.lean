-- Prove2me | solution 1 for VectorPayoffs.Convex.convex_approachable_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:58:19.437253+00:00
-- url     : https://prove2.me/submissions/0b5d8f4b-7873-4881-9a7d-941025082678

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game
import Theorems.Thm_VectorPayoffs_Convex_approachable_of_slack
import Theorems.Thm_VectorPayoffs_Convex_T_approachable_transpose
import Theorems.Thm_VectorPayoffs_Convex_transpose_excludable
import Theorems.Thm_VectorPayoffs_Convex_not_approachable_and_excludable

/-!
Blackwell (1956), Theorem 3: a closed convex set `S` is approachable iff it meets every `T(q)`, and
otherwise it is excludable with the stationary strategy `q₀` for which `S ∩ T(q₀) = ∅`.

Imported platform theorems: `T_approachable_transpose` (`T(q₀)` is approachable in the transpose with the
constant strategy), `transpose_excludable`, `not_approachable_and_excludable`, and the new
`approachable_of_slack` (Theorem 1 with separation error `κ/n`).

Proved here: the direction "`S` meets every `T(q)` implies approachable".  For each `x` the projection
`y = proj x` onto `S` gives the matrix `A(i,j) = ⟨x - y, m̄(i,j) - y⟩`; if `S` meets every `T(q)` then for
every column mixture some row has nonpositive payoff, and a matrix-game lemma proved from the
Hahn-Banach separation theorem (`exists_halfspace_strategy`) gives a row mixture with
`⟨x - y, w - y⟩ ≤ 0` on `R(p)`.  A *measurable* strategy is obtained without a selection theorem by
using, at stage `n`, the first point of a finite `1/n`-net of the simplex that satisfies the relaxed
inequality `≤ 1/n` (`exists_slack_strategy`); `approachable_of_slack` then applies.
-/

open MeasureTheory

namespace VectorPayoffs.Convex

namespace Game

variable {N r s : ℕ}

theorem exists_norm_bound (G : Game N r s) : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x ∈ G.X, ‖x‖ ≤ ρ := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp G.isBounded_X
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

/-- A closest point of a closed convex set, characterised by the variational inequality. -/
theorem exists_closest {K : Set (E N)} (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (x : E N) : ∃ y ∈ K, (∀ z ∈ K, dist x y ≤ dist x z) ∧ ∀ w ∈ K, inner ℝ (x - y) (w - y) ≤ 0 := by
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hc x
  refine ⟨y, hy, ?_, (norm_eq_iInf_iff_real_inner_le_zero hc hy).mp hmin⟩
  intro z hz
  rw [dist_eq_norm, dist_eq_norm, hmin]
  exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨z, hz⟩ : K)

/-- The projection onto a nonempty closed convex set (a choice of closest point). -/
noncomputable def proj {K : Set (E N)} (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (x : E N) : E N :=
  Classical.choose (exists_closest hK hc hne x)

theorem proj_mem {K : Set (E N)} (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (x : E N) : proj hK hc hne x ∈ K :=
  (Classical.choose_spec (exists_closest hK hc hne x)).1

theorem proj_min {K : Set (E N)} (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (x : E N) : ∀ z ∈ K, dist x (proj hK hc hne x) ≤ dist x z :=
  (Classical.choose_spec (exists_closest hK hc hne x)).2.1

theorem proj_inner {K : Set (E N)} (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (x : E N) : ∀ w ∈ K, inner ℝ (x - proj hK hc hne x) (w - proj hK hc hne x) ≤ 0 :=
  (Classical.choose_spec (exists_closest hK hc hne x)).2.2

theorem proj_lipschitz {K : Set (E N)} (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty) :
    LipschitzWith 1 (proj hK hc hne) := by
  refine LipschitzWith.of_dist_le_mul (fun x x' => ?_)
  set u := proj hK hc hne x with hu
  set u' := proj hK hc hne x' with hu'
  have h1 := proj_inner hK hc hne x u' (proj_mem hK hc hne x')
  have h2 := proj_inner hK hc hne x' u (proj_mem hK hc hne x)
  rw [← hu] at h1
  rw [← hu'] at h2
  have h3 : ‖u - u'‖ ^ 2 ≤ inner ℝ (x - x') (u - u') := by
    have e1 : inner ℝ (x - u) (u' - u) + inner ℝ (x' - u') (u - u') =
        inner ℝ (x - x') (u' - u) + ‖u - u'‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    have e2 : inner ℝ (x - x') (u' - u) = - inner ℝ (x - x') (u - u') := by
      rw [← inner_neg_right]; congr 1; abel
    linarith
  have h4 : inner ℝ (x - x') (u - u') ≤ ‖x - x'‖ * ‖u - u'‖ := real_inner_le_norm _ _
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  by_cases h0 : ‖u - u'‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖u - u'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem measurable_proj {K : Set (E N)} (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty) :
    Measurable (proj hK hc hne) :=
  (proj_lipschitz hK hc hne).continuous.measurable

/-- A matrix-game lemma (von Neumann): if for every mixed column strategy `q` some row has
nonpositive payoff, then some mixed row strategy has nonpositive payoff against every column. -/
theorem exists_halfspace_strategy (hr : 0 < r) (A : Fin r → Fin s → ℝ)
    (hq : ∀ q ∈ stdSimplex ℝ (Fin s), ∃ i, ∑ j, q j * A i j ≤ 0) :
    ∃ p ∈ stdSimplex ℝ (Fin r), ∀ j, ∑ i, p i * A i j ≤ 0 := by
  classical
  by_contra hno
  push Not at hno
  -- the linear map `p ↦ (∑ i p_i A i j)_j`
  let L : (Fin r → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
    { toFun := fun p j => ∑ i, p i * A i j
      map_add' := by intro p p'; ext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c p; ext j; simp [Finset.mul_sum, mul_assoc] }
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  set K : Set (Fin s → ℝ) := L '' stdSimplex ℝ (Fin r) with hK
  have hKc : IsCompact K := (isCompact_stdSimplex ℝ (Fin r)).image hL
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ (Fin r)).linear_image L
  set C : Set (Fin s → ℝ) := {u | ∀ j, u j ≤ 0} with hC
  have hCc : IsClosed C := by
    have : C = ⋂ j, {u : Fin s → ℝ | u j ≤ 0} := by ext u; simp [hC]
    rw [this]
    exact isClosed_iInter (fun j => isClosed_le (continuous_apply j) continuous_const)
  have hCconv : Convex ℝ C := by
    intro u hu v hv a b ha hb hab j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hu j, hv j]
  have hdisj : Disjoint K C := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ hC'
    obtain ⟨j, hj⟩ := hno p hp
    exact absurd (hC' j) (not_le.mpr hj)
  obtain ⟨f, u₀, v₀, hf1, huv, hf2⟩ := geometric_hahn_banach_compact_closed hKconv hKc hCconv hCc hdisj
  have h0 : v₀ < 0 := by
    have := hf2 0 (fun j => le_refl _)
    simpa using this
  -- `f (e_j) ≤ 0`
  have hfe : ∀ j, f (Pi.single j 1) ≤ 0 := by
    intro j
    by_contra hpos
    push Not at hpos
    set t : ℝ := (-v₀) / f (Pi.single j 1) + 1 with ht
    have ht0 : 0 ≤ t := by
      have : 0 ≤ (-v₀) / f (Pi.single j 1) := div_nonneg (by linarith) hpos.le
      linarith
    have hmem : (-t) • (Pi.single j (1 : ℝ) : Fin s → ℝ) ∈ C := by
      intro k
      by_cases hk : k = j
      · subst hk; simp; linarith
      · simp [hk]
    have := hf2 _ hmem
    rw [map_smul, smul_eq_mul] at this
    have h5 : -t * f (Pi.single j 1) = -(-v₀) - f (Pi.single j 1) := by
      rw [ht]; field_simp; ring
    nlinarith
  set w : Fin s → ℝ := fun j => - f (Pi.single j 1) with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => by simp only [hw]; linarith [hfe j]
  have hfsum : ∀ a : Fin s → ℝ, f a = - ∑ j, w j * a j := by
    intro a
    have : a = ∑ j, a j • (Pi.single j (1 : ℝ) : Fin s → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, hw, Finset.sum_neg_distrib, neg_mul, mul_neg, neg_neg]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hLp : ∀ p, L p = fun j => ∑ i, p i * A i j := fun p => rfl
  have hKmem : ∀ p ∈ stdSimplex ℝ (Fin r), f (L p) < u₀ := fun p hp => hf1 _ ⟨p, hp, rfl⟩
  have hu0 : u₀ < 0 := by linarith
  have hpos : ∀ p ∈ stdSimplex ℝ (Fin r), 0 < ∑ j, w j * ∑ i, p i * A i j := by
    intro p hp
    have := hKmem p hp
    rw [hfsum] at this
    simp only [hLp] at this
    linarith
  set W : ℝ := ∑ j, w j with hW
  have hWpos : 0 < W := by
    by_contra hW0
    have hz : ∀ j, w j = 0 := by
      intro j
      have h1 : W ≤ 0 := not_lt.mp hW0
      have h2 := Finset.single_le_sum (fun k _ => hw0 k) (Finset.mem_univ j)
      linarith [hw0 j]
    have := hpos (Pi.single ⟨0, hr⟩ 1) (single_mem_stdSimplex ℝ _)
    simp [hz] at this
  have hq' : (fun j => w j / W) ∈ stdSimplex ℝ (Fin s) := by
    refine ⟨fun j => div_nonneg (hw0 j) hWpos.le, ?_⟩
    rw [← Finset.sum_div]
    exact div_self hWpos.ne'
  obtain ⟨i, hi⟩ := hq _ hq'
  have := hpos (Pi.single i 1) (single_mem_stdSimplex ℝ _)
  have e : ∀ j, ∑ i', (Pi.single i (1 : ℝ) : Fin r → ℝ) i' * A i' j = A i j := by
    intro j
    simp [Pi.single_apply]
  simp only [e] at this
  have e2 : ∑ j, w j / W * A i j = (∑ j, w j * A i j) / W := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e2] at hi
  have := div_pos this hWpos
  linarith


instance instProbm (G : Game N r s) (i : Fin r) (j : Fin s) : IsProbabilityMeasure (G.m i j) :=
  G.isProb i j

theorem mbar_norm_le (G : Game N r s) {ρ : ℝ} (hρ : ∀ z ∈ G.X, ‖z‖ ≤ ρ) (i : Fin r)
    (j : Fin s) : ‖G.mbar i j‖ ≤ ρ := by
  unfold mbar
  have hae : ∀ᵐ z ∂(G.m i j), z ∈ G.X := by
    have := G.m_compl_X i j
    rw [← compl_mem_ae_iff] at this
    filter_upwards [this] with z hz using by simpa using hz
  refine (norm_integral_le_of_norm_le (integrable_const ρ) ?_).trans (by simp)
  filter_upwards [hae] with z hz using hρ z hz

/-- Pick the first element of a list satisfying a condition (or a default). -/
noncomputable def pick {α β : Type*} (c : α → β → Prop) (d : α) : List α → β → α
  | [], _ => d
  | p :: ps, x => by classical exact if c p x then p else pick c d ps x

theorem pick_mem {α β : Type*} (c : α → β → Prop) (d : α) (L : List α) (x : β) :
    pick c d L x = d ∨ pick c d L x ∈ L := by
  induction L with
  | nil => simp [pick]
  | cons p ps ih =>
    classical
    simp only [pick]
    split_ifs with h
    · right; simp
    · rcases ih with h1 | h1
      · left; exact h1
      · right; simp [h1]

theorem pick_spec {α β : Type*} (c : α → β → Prop) (d : α) (L : List α) (x : β)
    (h : ∃ p ∈ L, c p x) : c (pick c d L x) x := by
  induction L with
  | nil => simp at h
  | cons p ps ih =>
    classical
    simp only [pick]
    split_ifs with hc
    · exact hc
    · apply ih
      obtain ⟨q, hq, hcq⟩ := h
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact absurd hcq hc
      · exact ⟨q, hq', hcq⟩

theorem measurable_pick {α β : Type*} [MeasurableSpace β] [MeasurableSpace α]
    (c : α → β → Prop) (hc : ∀ p, MeasurableSet {x | c p x}) (d : α) (L : List α) :
    Measurable (pick c d L) := by
  induction L with
  | nil => exact measurable_const
  | cons p ps ih =>
    classical
    simp only [pick]
    exact Measurable.ite (hc p) measurable_const ih


theorem convex_inner_le (u p : E N) (c : ℝ) : Convex ℝ {w : E N | inner ℝ u (w - p) ≤ c} := by
  intro w₁ h₁ w₂ h₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have : a • w₁ + b • w₂ - p = a • (w₁ - p) + b • (w₂ - p) := by
    have hp : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [hp]
    simp only [smul_sub]
    abel
  rw [this, inner_add_right, inner_smul_right, inner_smul_right]
  have e : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb]

theorem convex_inner_gt (u p : E N) (c : ℝ) : Convex ℝ {w : E N | c < inner ℝ u (w - p)} := by
  intro w₁ h₁ w₂ h₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have : a • w₁ + b • w₂ - p = a • (w₁ - p) + b • (w₂ - p) := by
    have hp : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [hp]
    simp only [smul_sub]
    abel
  rw [this, inner_add_right, inner_smul_right, inner_smul_right]
  rcases ha.eq_or_lt with h0 | h0
  · subst h0
    have : b = 1 := by linarith
    subst this
    simpa using h₂
  · have e : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_pos h0 (sub_pos.mpr h₁), mul_nonneg hb (sub_pos.mpr h₂).le]

theorem inner_combo {k : ℕ} (w : Fin k → E N) (q : Fin k → ℝ) (hq : ∑ j, q j = 1) (u p : E N) :
    inner ℝ u (∑ j, q j • w j - p) = ∑ j, q j * inner ℝ u (w j - p) := by
  have : ∑ j, q j • w j - p = ∑ j, q j • (w j - p) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hq, one_smul]
  rw [this, inner_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [inner_smul_right])

theorem exists_slack_strategy (G : Game N r s) (hr : 1 ≤ r) (hs : 1 ≤ s) {S : Set (E N)}
    (hS : IsClosed S) (hSc : Convex ℝ S)
    (H : ∀ q ∈ stdSimplex ℝ (Fin s), (S ∩ G.T q).Nonempty) :
    ∃ f : Strategy N r, ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∈ G.X → avgHist h ∉ S →
      ∃ y ∈ S, (∀ z ∈ S, dist (avgHist h) y ≤ dist (avgHist h) z) ∧
        ∀ w ∈ G.R (f.toFun n h), inner ℝ (avgHist h - y) (w - y) ≤ 1 / (n : ℝ) := by
  classical
  have hr0 : 0 < r := hr
  have hne : S.Nonempty := by
    obtain ⟨t, ht, _⟩ := H (Pi.single ⟨0, hs⟩ 1) (single_mem_stdSimplex ℝ _)
    exact ⟨t, ht⟩
  set π := proj hS hSc hne with hπ
  have hπc : Continuous π := (proj_lipschitz hS hSc hne).continuous
  obtain ⟨ρ, hρ0, hρ⟩ := G.exists_norm_bound
  obtain ⟨s₀, hs₀⟩ := hne
  have hne : S.Nonempty := ⟨s₀, hs₀⟩
  set A0 : ℝ := ρ + ‖s₀‖ with hA0
  have hA00 : 0 ≤ A0 := by positivity
  set Cb : ℝ := A0 * (2 * ρ + A0) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  let Amat : E N → Fin r → Fin s → ℝ := fun x i j => inner ℝ (x - π x) (G.mbar i j - π x)
  -- exact optimal strategies exist
  have hexact : ∀ x : E N, ∃ p ∈ stdSimplex ℝ (Fin r), ∀ j, ∑ i, p i * Amat x i j ≤ 0 := by
    intro x
    refine exists_halfspace_strategy hr0 (Amat x) (fun q hq => ?_)
    obtain ⟨t, htS, htT⟩ := H q hq
    by_contra hall
    push Not at hall
    have hsub : Set.range (fun i : Fin r => ∑ j, q j • G.mbar i j) ⊆
        {w : E N | 0 < inner ℝ (x - π x) (w - π x)} := by
      rintro _ ⟨i, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [inner_combo _ q hq.2]
      exact hall i
    have := convexHull_min hsub (convex_inner_gt (x - π x) (π x) 0) htT
    have h2 := proj_inner hS hSc hne x t htS
    simp only [Set.mem_setOf_eq] at this
    linarith
  have hAbound : ∀ x ∈ G.X, ∀ i j, |Amat x i j| ≤ Cb := by
    intro x hx i j
    have h1 : ‖x - π x‖ ≤ A0 := by
      have := proj_min hS hSc hne x s₀ hs₀
      rw [dist_eq_norm, dist_eq_norm] at this
      exact this.trans ((norm_sub_le _ _).trans (add_le_add (hρ x hx) le_rfl))
    have h2 : ‖G.mbar i j - π x‖ ≤ 2 * ρ + A0 := by
      have a1 : ‖G.mbar i j - π x‖ ≤ ‖G.mbar i j - x‖ + ‖x - π x‖ := by
        calc ‖G.mbar i j - π x‖ = ‖(G.mbar i j - x) + (x - π x)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have a2 : ‖G.mbar i j - x‖ ≤ 2 * ρ :=
        (norm_sub_le _ _).trans (by linarith [mbar_norm_le G hρ i j, hρ x hx])
      linarith
    calc |Amat x i j| = ‖inner ℝ (x - π x) (G.mbar i j - π x)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x - π x‖ * ‖G.mbar i j - π x‖ := norm_inner_le_norm _ _
      _ ≤ A0 * (2 * ρ + A0) := mul_le_mul h1 h2 (norm_nonneg _) hA00
  -- finite nets of the simplex
  have hnet : ∀ n : ℕ, ∃ P : Finset (Fin r → ℝ), (∀ p ∈ P, p ∈ stdSimplex ℝ (Fin r)) ∧
      ∀ p ∈ stdSimplex ℝ (Fin r), ∃ p' ∈ P,
        ∀ i, |p i - p' i| ≤ 1 / (((max n 1 : ℕ) : ℝ) * ((r : ℝ) * Cb + 1)) := by
    intro n
    have hn1 : (0 : ℝ) < ((max n 1 : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le one_pos (le_max_right n 1))
    have he : 0 < 1 / (((max n 1 : ℕ) : ℝ) * ((r : ℝ) * Cb + 1)) := by positivity
    obtain ⟨t, hts, htf, hcov⟩ := (isCompact_stdSimplex ℝ (Fin r)).finite_cover_balls he
    refine ⟨htf.toFinset, fun p hp => hts (by simpa using hp), fun p hp => ?_⟩
    have := hcov hp
    simp only [Set.mem_iUnion] at this
    obtain ⟨p', hp't, hball⟩ := this
    refine ⟨p', by simpa using hp't, fun i => ?_⟩
    have h1 := dist_le_pi_dist p p' i
    rw [Real.dist_eq] at h1
    have h2 : dist p p' < 1 / (((max n 1 : ℕ) : ℝ) * ((r : ℝ) * Cb + 1)) := Metric.mem_ball.mp hball
    linarith
  choose P hPs hPcov using hnet
  let cond : ℕ → (Fin r → ℝ) → E N → Prop := fun n p x =>
    ∀ j, ∑ i, p i * Amat x i j ≤ 1 / ((max n 1 : ℕ) : ℝ)
  let d₀ : Fin r → ℝ := Pi.single ⟨0, hr0⟩ 1
  have hd₀ : d₀ ∈ stdSimplex ℝ (Fin r) := single_mem_stdSimplex ℝ _
  let sel : ℕ → E N → (Fin r → ℝ) := fun n => pick (cond n) d₀ (P n).toList
  have hcm : ∀ n p, MeasurableSet {x | cond n p x} := by
    intro n p
    have : {x | cond n p x} = ⋂ j, {x : E N | ∑ i, p i * Amat x i j ≤ 1 / ((max n 1 : ℕ) : ℝ)} := by
      ext x; simp [cond]
    rw [this]
    refine (isClosed_iInter (fun j => isClosed_le ?_ continuous_const)).measurableSet
    refine continuous_finset_sum _ (fun i _ => continuous_const.mul ?_)
    exact (continuous_id.sub hπc).inner (continuous_const.sub hπc)
  have hsel_meas : ∀ n, Measurable (sel n) := fun n => measurable_pick (cond n) (hcm n) d₀ _
  have hsel_mem : ∀ n x, sel n x ∈ stdSimplex ℝ (Fin r) := by
    intro n x
    rcases pick_mem (cond n) d₀ (P n).toList x with h | h
    · show pick (cond n) d₀ (P n).toList x ∈ stdSimplex ℝ (Fin r)
      rw [h]; exact hd₀
    · exact hPs n _ (Finset.mem_toList.mp h)
  have hsel_spec : ∀ n x, x ∈ G.X → cond n (sel n x) x := by
    intro n x hx
    apply pick_spec
    obtain ⟨p, hp, hpj⟩ := hexact x
    obtain ⟨p', hp'P, hp'⟩ := hPcov n p hp
    refine ⟨p', Finset.mem_toList.mpr hp'P, fun j => ?_⟩
    have hnn : (0 : ℝ) < ((max n 1 : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le one_pos (le_max_right n 1))
    set η : ℝ := 1 / (((max n 1 : ℕ) : ℝ) * ((r : ℝ) * Cb + 1)) with hη
    have h1 : ∑ i, p' i * Amat x i j ≤ ∑ i, p i * Amat x i j + ∑ i : Fin r, η * Cb := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have a1 : |(p' i - p i) * Amat x i j| ≤ η * Cb := by
        rw [abs_mul]
        have : |p' i - p i| ≤ η := by rw [abs_sub_comm]; exact hp' i
        exact mul_le_mul this (hAbound x hx i j) (abs_nonneg _) (by positivity)
      have := (abs_le.mp a1).2
      nlinarith [this]
    have h2 : ∑ i : Fin r, η * Cb = (r : ℝ) * (η * Cb) := by simp
    have h3 : (r : ℝ) * (η * Cb) ≤ 1 / ((max n 1 : ℕ) : ℝ) := by
      rw [hη, show (r : ℝ) * (1 / (((max n 1 : ℕ) : ℝ) * ((r : ℝ) * Cb + 1)) * Cb) =
        ((r : ℝ) * Cb) / (((max n 1 : ℕ) : ℝ) * ((r : ℝ) * Cb + 1)) by ring]
      rw [div_le_div_iff₀ (by positivity) hnn]
      have : (0 : ℝ) ≤ (r : ℝ) * Cb := by positivity
      nlinarith
    linarith [hpj j]
  have havgmeas : ∀ n : ℕ, Measurable (fun h : Fin n → E N => avgHist h) := by
    intro n
    unfold avgHist
    have hsum : Measurable (fun h : Fin n → E N => ∑ k, h k) :=
      Finset.measurable_sum _ (fun k _ => measurable_pi_apply k)
    exact hsum.const_smul ((n : ℝ)⁻¹)
  refine ⟨⟨fun n h => sel n (avgHist h), fun n h => hsel_mem n _,
    fun n => (hsel_meas n).comp (havgmeas n)⟩, ?_⟩
  intro n hn h hX hxS
  refine ⟨π (avgHist h), proj_mem hS hSc hne _, proj_min hS hSc hne _, ?_⟩
  intro w hw
  have hcond := hsel_spec n (avgHist h) hX
  have hmax : max n 1 = n := max_eq_left hn
  have hpmem := hsel_mem n (avgHist h)
  set p := sel n (avgHist h) with hp
  have hsub : Set.range (fun j : Fin s => ∑ i, p i • G.mbar i j) ⊆
      {w : E N | inner ℝ (avgHist h - π (avgHist h)) (w - π (avgHist h)) ≤ 1 / (n : ℝ)} := by
    rintro _ ⟨j, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [inner_combo _ p hpmem.2]
    have := hcond j
    rw [hmax] at this
    exact this
  exact convexHull_min hsub (convex_inner_le _ _ _) hw


theorem convex_approachable_iff_proof {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (S : Set (E N)) (hS : IsClosed S) (hSc : Convex ℝ S) :
    (G.ApproachableIn S ↔ ∀ q ∈ stdSimplex ℝ (Fin s), (S ∩ G.T q).Nonempty) ∧
      ∀ (q₀ : Fin s → ℝ) (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)), S ∩ G.T q₀ = ∅ →
        G.ExcludableWith S (Strategy.const q₀ hq₀) := by
  classical
  have hexc : ∀ (q₀ : Fin s → ℝ) (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)), S ∩ G.T q₀ = ∅ →
      G.ExcludableWith S (Strategy.const q₀ hq₀) := by
    intro q₀ hq₀ hemp
    have hTc : IsClosed (G.T q₀) := by
      unfold T
      exact ((Set.finite_range _).isCompact_convexHull ℝ).isClosed
    have hdisj : Disjoint (G.T q₀) S := by
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]; exact hemp
    exact transpose_excludable G (G.T q₀) S hTc hS hdisj (Strategy.const q₀ hq₀)
      (T_approachable_transpose G q₀ hq₀)
  refine ⟨⟨?_, ?_⟩, hexc⟩
  · rintro hApp q hq
    by_contra hno
    rw [Set.not_nonempty_iff_eq_empty] at hno
    exact not_approachable_and_excludable G hr hs S ⟨hApp, ⟨_, hexc q hq hno⟩⟩
  · intro H
    obtain ⟨f, hslack⟩ := exists_slack_strategy G hr hs hS hSc H
    exact ⟨f, approachable_of_slack G S 1 zero_le_one f hslack⟩

end Game

end VectorPayoffs.Convex

open VectorPayoffs.Convex in
theorem solution {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (S : Set (E N)) (hS : IsClosed S) (hSc : Convex ℝ S) :
    (G.ApproachableIn S ↔ ∀ q ∈ stdSimplex ℝ (Fin s), (S ∩ G.T q).Nonempty) ∧
      ∀ (q₀ : Fin s → ℝ) (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)), S ∩ G.T q₀ = ∅ →
        G.ExcludableWith S (Strategy.const q₀ hq₀) :=
  Game.convex_approachable_iff_proof G hr hs S hS hSc
