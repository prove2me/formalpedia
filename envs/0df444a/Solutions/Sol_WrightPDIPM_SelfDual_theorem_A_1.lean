-- Prove2me | solution 1 for WrightPDIPM.SelfDual.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:39:29.231933+00:00
-- url     : https://prove2.me/submissions/e3657b86-d973-475f-b7ac-f74410ebf2db

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup
open WrightPDIPM.SelfDual
open Matrix

theorem g69a1_cara {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E] (v : ι → E)
    (t : Finset ι) : ∀ l : ι → ℝ, (∀ i, 0 ≤ l i) → ∃ s ⊆ t, ∃ l' : ι → ℝ, (∀ i, 0 ≤ l' i) ∧
      LinearIndepOn ℝ v (s : Set ι) ∧ ∑ i ∈ s, l' i • v i = ∑ i ∈ t, l i • v i := by
  induction t using Finset.strongInduction with
  | H t ih =>
  intro l hl
  by_cases hli : LinearIndepOn ℝ v (t : Set ι)
  · exact ⟨t, subset_rfl, l, hl, hli, rfl⟩
  rw [not_linearIndepOn_finset_iffₛ] at hli
  obtain ⟨f, g, hfg, i0, hi0t, hi0⟩ := hli
  have hsum0 : ∑ i ∈ t, (f i - g i) • v i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hfg, sub_self]
  -- get ν supported on t with positive entry
  obtain ⟨ν, hνsum, hνsupp, i1, hi1t, hi1⟩ : ∃ ν : ι → ℝ, ∑ i ∈ t, ν i • v i = 0 ∧
      (∀ i, i ∉ t → ν i = 0) ∧ ∃ i ∈ t, 0 < ν i := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hi0) with h | h
    · refine ⟨fun i => if i ∈ t then -(f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then -(f i - g i) else 0) • v i = -((f i - g i) • v i) := by
          intro i hi; rw [if_pos hi, neg_smul]
        beta_reduce
        rw [Finset.sum_congr rfl hc, Finset.sum_neg_distrib, hsum0, neg_zero]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
    · refine ⟨fun i => if i ∈ t then (f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then (f i - g i) else 0) • v i = (f i - g i) • v i := by
          intro i hi; rw [if_pos hi]
        beta_reduce
        rw [Finset.sum_congr rfl hc, hsum0]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
  set P := t.filter (fun i => 0 < ν i) with hP
  have hPne : P.Nonempty := ⟨i1, by simp [hP, hi1t, hi1]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image P (fun i => l i / ν i) hPne
  have hjt : j ∈ t := (Finset.mem_filter.mp hjP).1
  have hjpos : 0 < ν j := (Finset.mem_filter.mp hjP).2
  set θ := l j / ν j with hθ
  have hθnn : 0 ≤ θ := div_nonneg (hl j) hjpos.le
  set l' : ι → ℝ := fun i => l i - θ * ν i with hl'
  have hl'nn : ∀ i, 0 ≤ l' i := by
    intro i
    simp only [hl']
    by_cases hit : i ∈ t
    · by_cases hνi : 0 < ν i
      · have hiP : i ∈ P := by simp [hP, hit, hνi]
        have := hjmin i hiP
        rw [le_div_iff₀ hνi] at this
        linarith
      · push Not at hνi
        nlinarith [hl i]
    · rw [hνsupp i hit]; simp [hl i]
  have hl'j : l' j = 0 := by
    simp only [hl', hθ]; field_simp; ring
  have hsum' : ∑ i ∈ t.erase j, l' i • v i = ∑ i ∈ t, l i • v i := by
    rw [Finset.sum_erase _ (by rw [hl'j, zero_smul])]
    simp only [hl', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hνsum,
      smul_zero, sub_zero]
  obtain ⟨s, hs, l'', hl'', hli, hs'⟩ := ih (t.erase j) (Finset.erase_ssubset hjt) l' hl'nn
  exact ⟨s, hs.trans (Finset.erase_subset _ _), l'', hl'', hli, hs'.trans hsum'⟩

theorem g69a1_cone_closed {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] (v : ι → κ → ℝ) :
    IsClosed {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} := by
  classical
  have heq : {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} =
      ⋃ s ∈ {s : Finset ι | LinearIndepOn ℝ v (s : Set ι)},
        (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) '' {m | ∀ i, 0 ≤ m i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨s, -, l', hl', hli, hs⟩ := g69a1_cara v Finset.univ l hl
      refine ⟨s, hli, fun i => l' i, fun i => hl' i, ?_⟩
      rw [Fintype.linearCombination_apply, ← hs]
      exact (Finset.sum_coe_sort s (fun i => l' i • v i))
    · rintro ⟨s, -, m, hm, rfl⟩
      refine ⟨fun i => if h : i ∈ s then m ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i; by_cases h : i ∈ s <;> simp [h, hm]
      · rw [Fintype.linearCombination_apply]
        rw [← Finset.sum_subset (Finset.subset_univ s)]
        · rw [← Finset.sum_coe_sort s]
          apply Finset.sum_congr rfl
          intro i _
          simp
        · intro i _ hi; simp [hi]
  rw [heq]
  apply Set.Finite.isClosed_biUnion (Set.toFinite _)
  intro s hs
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (linearIndependent_iff_injective_fintypeLinearCombination).mp hs
  apply (LinearMap.isClosedEmbedding_of_injective hinj).isClosedMap
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

theorem g69a1_farkas {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : ι → κ → ℝ) (a : κ → ℝ)
    (ha : ¬ ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ a = ∑ i, l i • v i) :
    ∃ x : κ → ℝ, a ⬝ᵥ x < 0 ∧ ∀ i, 0 ≤ v i ⬝ᵥ x := by
  classical
  set C := {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} with hC
  have hconv : Convex ℝ C := by
    rintro y ⟨l, hl, rfl⟩ z ⟨m, hm, rfl⟩ α β hα hβ _
    refine ⟨fun i => α * l i + β * m i, fun i => by have := hl i; have := hm i; positivity, ?_⟩
    simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]
  obtain ⟨f, u, hfa, hfC⟩ := geometric_hahn_banach_point_closed hconv (g69a1_cone_closed v) ha
  have hu : u < 0 := by
    have := hfC 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hfnn : ∀ y ∈ C, 0 ≤ f y := by
    intro y hy
    by_contra hneg
    push Not at hneg
    obtain ⟨l, hl, rfl⟩ := hy
    set t : ℝ := u / f (∑ i, l i • v i) with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg hu hneg
    have hmem : t • (∑ i, l i • v i) ∈ C :=
      ⟨fun i => t * l i, fun i => mul_nonneg htpos.le (hl i), by
        simp only [Finset.smul_sum, mul_smul]⟩
    have := hfC _ hmem
    rw [map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  let x : κ → ℝ := fun j => f (Pi.single j 1)
  have hfx : ∀ y : κ → ℝ, f y = y ⬝ᵥ x := by
    intro y
    conv_lhs => rw [show y = ∑ j, y j • Pi.single j (1:ℝ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, dotProduct, x]
  refine ⟨x, ?_, ?_⟩
  · rw [← hfx]; linarith
  · intro i
    rw [← hfx]
    apply hfnn
    refine ⟨Pi.single i 1, fun j => ?_, ?_⟩
    · by_cases h : j = i <;> simp [Pi.single_apply, h]
    · simp [Pi.single_apply]



open Filter Topology in
theorem g70wr_dir {N k l : ℕ} (f : (Fin N → ℝ) → ℝ) (C : Matrix (Fin k) (Fin N) ℝ)
    (d : Fin k → ℝ) (G : Matrix (Fin l) (Fin N) ℝ) (h : Fin l → ℝ) (U : Set (Fin N → ℝ))
    (hU : IsOpen U) (ustar : Fin N → ℝ) (hloc : IsLocalSolutionA2 f C d G h U ustar)
    (hD : DifferentiableAt ℝ f ustar) (v : Fin N → ℝ) (hCv : C *ᵥ v = 0)
    (hGv : ∀ i, (G *ᵥ ustar) i = h i → 0 ≤ (G *ᵥ v) i) :
    0 ≤ fderiv ℝ f ustar v := by
  obtain ⟨⟨hUs, hCs, hGs⟩, ρ, hρ, hmin⟩ := hloc
  have hφ : HasDerivAt (fun t : ℝ => f (ustar + t • v)) (fderiv ℝ f ustar v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ustar + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ustar
    have h2 : HasFDerivAt f (fderiv ℝ f ustar) (ustar + (0 : ℝ) • v) := by
      simpa using hD.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hcont : Continuous (fun t : ℝ => ustar + t • v) := by fun_prop
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f ustar ≤ f (ustar + t • v) := by
    have e1 : ∀ᶠ t in 𝓝 (0 : ℝ), ustar + t • v ∈ U := by
      apply hcont.continuousAt.preimage_mem_nhds
      simpa using hU.mem_nhds hUs
    have e2 : ∀ᶠ t in 𝓝 (0 : ℝ), norm2 (ustar + t • v - ustar) < ρ := by
      have hc : Continuous (fun t : ℝ => norm2 (ustar + t • v - ustar)) := by
        unfold norm2; fun_prop
      have : norm2 (ustar + (0 : ℝ) • v - ustar) < ρ := by simp [norm2]; exact hρ
      exact hc.continuousAt.eventually_lt continuousAt_const this
    have e3 : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), h i ≤ (G *ᵥ (ustar + t • v)) i := by
      intro i
      rcases (hGs i).lt_or_eq with hlt | heq
      · apply eventually_nhdsWithin_of_eventually_nhds
        have hc : Continuous (fun t : ℝ => (G *ᵥ (ustar + t • v)) i) := by
          simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          fun_prop
        have : h i < (G *ᵥ (ustar + (0 : ℝ) • v)) i := by simpa using hlt
        exact (continuousAt_const.eventually_lt hc.continuousAt this).mono fun t ht => ht.le
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have := hGv i heq.symm
        simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have : 0 ≤ t * (G *ᵥ v) i := mul_nonneg (le_of_lt ht) this
        linarith
    have e3' := (Filter.eventually_all.2 e3)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds e1,
      eventually_nhdsWithin_of_eventually_nhds e2, e3'] with t h1 h2 h3
    apply hmin _ ⟨h1, ?_, h3⟩ h2
    rw [mulVec_add, mulVec_smul, hCv, smul_zero, add_zero, hCs]
  have hlim := hφ.tendsto_slope_zero_right
  refine ge_of_tendsto hlim ?_
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htp
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt htp)) (by linarith)

theorem g70wr_lin {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ) (v : Fin N → ℝ) :
    L v = (fun i => L (Pi.single i (1 : ℝ))) ⬝ᵥ v := by
  have := LinearMap.pi_apply_eq_sum_univ (L : (Fin N → ℝ) →ₗ[ℝ] ℝ) v
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]


open Matrix

/-- Theorem A.1 (pp. 240–241): if `u*` is a local solution of (A.2)
`min f(u) s.t. Cu = d, Gu ≥ h, u ∈ U` (`U ⊂ ℝᴺ` open) and `f` is differentiable in a
neighborhood of `u*`, then there are Lagrange multipliers `y`, `z` with (A.3a)
`∇f(u*) − Cᵀy − Gᵀz = 0`, (A.3b) `Cu* = d`, (A.3c) `Gu* ≥ h`, (A.3d) `z ≥ 0`,
(A.3e) `zᵀ(Gu* − h) = 0`. -/
theorem solution {N k l : ℕ} (f : (Fin N → ℝ) → ℝ) (C : Matrix (Fin k) (Fin N) ℝ)
    (d : Fin k → ℝ) (G : Matrix (Fin l) (Fin N) ℝ) (h : Fin l → ℝ) (U : Set (Fin N → ℝ))
    (hU : IsOpen U) (ustar : Fin N → ℝ) (hloc : IsLocalSolutionA2 f C d G h U ustar)
    (hdiff : ∀ᶠ u in nhds ustar, DifferentiableAt ℝ f u) :
    ∃ (y : Fin k → ℝ) (z : Fin l → ℝ),
      gradVec f ustar - Cᵀ *ᵥ y - Gᵀ *ᵥ z = 0 ∧
      C *ᵥ ustar = d ∧
      (∀ i, h i ≤ (G *ᵥ ustar) i) ∧
      (∀ i, 0 ≤ z i) ∧
      z ⬝ᵥ (G *ᵥ ustar - h) = 0 := by
  classical
  have hD : DifferentiableAt ℝ f ustar := hdiff.self_of_nhds
  have hfeas := hloc.1
  set gr := gradVec f ustar with hgr
  let act : Fin l → Prop := fun i => (G *ᵥ ustar) i = h i
  let V : Fin k ⊕ Fin k ⊕ Fin l → Fin N → ℝ :=
    Sum.elim (fun r => C r) (Sum.elim (fun r => -C r) (fun i => if act i then G i else 0))
  have hcone : ∃ L : Fin k ⊕ Fin k ⊕ Fin l → ℝ, (∀ o, 0 ≤ L o) ∧ gr = ∑ o, L o • V o := by
    by_contra hne
    obtain ⟨v, hv, hV⟩ := g69a1_farkas V gr hne
    have hCv : C *ᵥ v = 0 := by
      funext r
      have h1 := hV (Sum.inl r)
      have h2 := hV (Sum.inr (Sum.inl r))
      simp only [V, Sum.elim_inl, Sum.elim_inr, neg_dotProduct] at h1 h2
      simp only [mulVec, Pi.zero_apply]
      linarith
    have hGv : ∀ i, (G *ᵥ ustar) i = h i → 0 ≤ (G *ᵥ v) i := fun i hi => by
      have := hV (Sum.inr (Sum.inr i))
      simp only [V, Sum.elim_inr, act, if_pos hi] at this
      simpa [mulVec] using this
    have h0 := g70wr_dir f C d G h U hU ustar hloc hD v hCv hGv
    rw [g70wr_lin] at h0
    exact absurd hv (not_lt.mpr h0)
  obtain ⟨L, hL, hgL⟩ := hcone
  refine ⟨fun r => L (Sum.inl r) - L (Sum.inr (Sum.inl r)),
    fun i => if act i then L (Sum.inr (Sum.inr i)) else 0, ?_, hfeas.2.1, hfeas.2.2,
    fun i => by dsimp only; split_ifs <;> simp [hL], ?_⟩
  · rw [hgL]
    funext j
    simp only [Fintype.sum_sum_type, V, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply,
      Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.zero_apply]
    simp only [mulVec, dotProduct, transpose_apply]
    have : ∀ i, L (Sum.inr (Sum.inr i)) * (if act i then G i else 0) j =
        G i j * (if act i then L (Sum.inr (Sum.inr i)) else 0) := fun i => by
      split_ifs <;> simp [mul_comm]
    simp only [this, mul_sub, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
    have e : ∀ r, C r j * L (Sum.inl r) = L (Sum.inl r) * C r j := fun r => mul_comm _ _
    have e2 : ∀ r, C r j * L (Sum.inr (Sum.inl r)) = L (Sum.inr (Sum.inl r)) * C r j :=
      fun r => mul_comm _ _
    simp only [e, e2]
    ring
  · simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hi
    · simp only [Pi.sub_apply]; rw [hi]; ring
    · simp

