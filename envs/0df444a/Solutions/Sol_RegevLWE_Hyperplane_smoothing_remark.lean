-- Prove2me | solution 1 for RegevLWE.Hyperplane.smoothing_remark
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T21:35:32.806534+00:00
-- url     : https://prove2.me/submissions/44fbad4d-c0b3-4372-aae2-2b5a8ef2d6e6

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian

open Filter Topology RegevLWE.Hyperplane RegevLWE.GaussConv

private lemma inner_nondegenerate (n : ℕ) :
    (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun x hx => inner_self_eq_zero.mp (hx x)⟩

private lemma dual_eq_span {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n))),
      dual L = Submodule.span ℤ (Set.range b) := by
  classical
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b₀ := Module.Free.chooseBasis ℤ ↥L
  let b := b₀.ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := b₀.ofZLatticeBasis_span ℝ
  refine ⟨Module.Free.ChooseBasisIndex ℤ ↥L, inferInstance,
    LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n) b, ?_⟩
  change LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n))) L = _
  conv_lhs => rw [← hspan]
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis
    (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n) b

private instance instDiscreteTopologyDual {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (dual L) := by
  obtain ⟨ι, _, b, h⟩ := dual_eq_span L
  rw [h]
  infer_instance

private instance instIsZLatticeDual {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    IsZLattice ℝ (dual L) := by
  obtain ⟨ι, _, b, h⟩ := dual_eq_span L
  exact ⟨by rw [h]; exact ZSpan.span_top b⟩

private lemma nonempty_nonzero_lattice {n : ℕ} (hn : 0 < n)
    (M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology M] [IsZLattice ℝ M] :
    Nonempty {y : M // y ≠ 0} := by
  have hrank : 0 < Module.finrank ℤ M := by
    rw [ZLattice.rank ℝ M, finrank_euclideanSpace_fin]
    exact hn
  have : Nontrivial M := Module.finrank_pos_iff.mp hrank
  obtain ⟨y, hy⟩ := exists_ne (0 : M)
  exact ⟨⟨y, hy⟩⟩

private lemma nsmul_norm {n : ℕ} {M : Submodule ℤ (EuclideanSpace ℝ (Fin n))} (k : ℕ) (y : M) :
    ‖(k • y : M)‖ = (k : ℝ) * ‖y‖ := by
  change ‖((k • y : M) : EuclideanSpace ℝ (Fin n))‖ = (k : ℝ) * ‖(y : EuclideanSpace ℝ (Fin n))‖
  rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
    Real.norm_of_nonneg (Nat.cast_nonneg k)]

private lemma infinite_nonzero_lattice {n : ℕ} (hn : 0 < n)
    (M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology M] [IsZLattice ℝ M] :
    Infinite {y : M // y ≠ 0} := by
  obtain ⟨⟨y₀, hy₀⟩⟩ := nonempty_nonzero_lattice hn M
  have hy₀_pos : 0 < ‖y₀‖ := norm_pos_iff.mpr hy₀
  refine Infinite.of_injective (fun k : ℕ => (⟨(k + 1) • y₀, ?_⟩ : {y : M // y ≠ 0})) ?_
  · refine norm_pos_iff.mp ?_
    rw [nsmul_norm]
    positivity
  · intro a b hab
    have hval : ((a + 1) • y₀ : M) = (b + 1) • y₀ := Subtype.ext_iff.mp hab
    have hnorm : ‖((a + 1) • y₀ : M)‖ = ‖((b + 1) • y₀ : M)‖ := congr_arg norm hval
    rw [nsmul_norm, nsmul_norm] at hnorm
    have hcast : ((a + 1 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) := mul_right_cancel₀ hy₀_pos.ne' hnorm
    exact Nat.succ.inj (Nat.cast_injective hcast)

private lemma rho_one_div {n : ℕ} (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    rho (1 / s) x = Real.exp (-Real.pi * s ^ 2 * ‖x‖ ^ 2) := by
  unfold rho
  rw [one_div, inv_pow, div_inv_eq_mul]
  ring_nf

private noncomputable def dualBound {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (s₀ : ℝ) (y : {y : dual L // y ≠ 0}) : ℝ :=
  let k := Module.finrank ℤ (dual L) + 1
  ((k.factorial : ℝ) / (Real.pi * s₀ ^ 2) ^ k) * (‖(y : dual L)‖⁻¹ ^ (2 * k))

private lemma summable_dualBound {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (s₀ : ℝ) :
    Summable (dualBound L s₀) := by
  let k := Module.finrank ℤ (dual L) + 1
  have hk : Module.finrank ℤ (dual L) < 2 * k := by omega
  have hsum : Summable (fun z : dual L => ‖z‖⁻¹ ^ (2 * k)) :=
    ZLattice.summable_norm_pow_inv (dual L) (2 * k) hk
  exact (hsum.comp_injective Subtype.val_injective).mul_left _

private lemma rho_le_dualBound {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (y : {y : dual L // y ≠ 0}) :
    ‖rho (1 / s) ((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ≤ dualBound L s₀ y := by
  rw [Real.norm_of_nonneg (by unfold rho; positivity), rho_one_div]
  let k := Module.finrank ℤ (dual L) + 1
  have hy : 0 < ‖(y : dual L)‖ := norm_pos_iff.mpr y.2
  have hy' : ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ = ‖(y : dual L)‖ := rfl
  rw [hy']
  have hs_pos : 0 < s := hs₀.trans_le hs
  have h_arg_nonneg : 0 ≤ Real.pi * s ^ 2 * ‖(y : dual L)‖ ^ 2 := by positivity
  have h2 : (Real.pi * s₀ ^ 2 * ‖(y : dual L)‖ ^ 2) ^ k / (k.factorial : ℝ) ≤
      Real.exp (Real.pi * s ^ 2 * ‖(y : dual L)‖ ^ 2) := by
    calc (Real.pi * s₀ ^ 2 * ‖(y : dual L)‖ ^ 2) ^ k / (k.factorial : ℝ)
        ≤ (Real.pi * s ^ 2 * ‖(y : dual L)‖ ^ 2) ^ k / (k.factorial : ℝ) := by gcongr
      _ ≤ Real.exp (Real.pi * s ^ 2 * ‖(y : dual L)‖ ^ 2) :=
        Real.pow_div_factorial_le_exp _ h_arg_nonneg k
  have h3 : -Real.pi * s ^ 2 * ‖(y : dual L)‖ ^ 2 = -(Real.pi * s ^ 2 * ‖(y : dual L)‖ ^ 2) := by ring
  rw [h3, Real.exp_neg]
  have h_pos_lhs : 0 < (Real.pi * s₀ ^ 2 * ‖(y : dual L)‖ ^ 2) ^ k / (k.factorial : ℝ) := by positivity
  have h4 : (Real.exp (Real.pi * s ^ 2 * ‖(y : dual L)‖ ^ 2))⁻¹ ≤
      ((Real.pi * s₀ ^ 2 * ‖(y : dual L)‖ ^ 2) ^ k / (k.factorial : ℝ))⁻¹ :=
    inv_anti₀ h_pos_lhs h2
  refine h4.trans_eq ?_
  dsimp [dualBound, k]
  rw [inv_div, mul_pow, ← pow_mul, div_eq_mul_inv, mul_inv]
  ring

private lemma summable_rho_dual {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {s : ℝ} (hs : 0 < s) :
    Summable (fun y : {y : dual L // y ≠ 0} => rho (1 / s) ((y : dual L) : EuclideanSpace ℝ (Fin n))) := by
  refine (summable_dualBound L s).of_norm_bounded (fun y => ?_)
  exact rho_le_dualBound L hs le_rfl y

private lemma continuousOn_rhoDualNonzero {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ContinuousOn (fun s : ℝ => rhoDualNonzero (1 / s) L) (Set.Ioi 0) := by
  rw [isOpen_Ioi.continuousOn_iff]
  intro s hs
  have hs2 : 0 < s / 2 := half_pos hs
  have h_cont : ContinuousOn (fun t : ℝ => rhoDualNonzero (1 / t) L) (Set.Ici (s / 2)) := by
    unfold rhoDualNonzero
    refine continuousOn_tsum (fun y => ?_) (summable_dualBound L (s / 2)) (fun y t ht => ?_)
    · simp_rw [rho_one_div]
      fun_prop
    · exact rho_le_dualBound L hs2 ht y
  exact h_cont.continuousAt (Ici_mem_nhds (half_lt_self hs))

private lemma strictAntiOn_rhoDualNonzero {n : ℕ} (hn : 0 < n)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L] :
    StrictAntiOn (fun s : ℝ => rhoDualNonzero (1 / s) L) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold rhoDualNonzero
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  obtain ⟨y₀⟩ := nonempty_nonzero_lattice hn (dual L)
  have hle : ∀ y : {y : dual L // y ≠ 0},
      rho (1 / b) ((y : dual L) : EuclideanSpace ℝ (Fin n)) ≤
        rho (1 / a) ((y : dual L) : EuclideanSpace ℝ (Fin n)) := by
    intro y
    rw [rho_one_div, rho_one_div, Real.exp_le_exp]
    have h1 : Real.pi * a ^ 2 * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
        Real.pi * b ^ 2 * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by gcongr
    linarith
  have hlt : rho (1 / b) ((y₀ : dual L) : EuclideanSpace ℝ (Fin n)) <
      rho (1 / a) ((y₀ : dual L) : EuclideanSpace ℝ (Fin n)) := by
    rw [rho_one_div, rho_one_div, Real.exp_lt_exp]
    have hy₀ : 0 < ‖((y₀ : dual L) : EuclideanSpace ℝ (Fin n))‖ :=
      norm_pos_iff.mpr (Submodule.coe_eq_zero.not.mpr y₀.2)
    have h1 : Real.pi * a ^ 2 * ‖((y₀ : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2 <
        Real.pi * b ^ 2 * ‖((y₀ : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by gcongr
    linarith
  exact Summable.tsum_lt_tsum hle hlt (summable_rho_dual L hb') (summable_rho_dual L ha')

private lemma tendsto_zero_rhoDualNonzero {n : ℕ} (hn : 0 < n)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Tendsto (fun s : ℝ => rhoDualNonzero (1 / s) L) (𝓝[>] 0) atTop := by
  rw [Filter.tendsto_atTop]
  intro C
  have : Infinite {y : dual L // y ≠ 0} := infinite_nonzero_lattice hn (dual L)
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq ({y : dual L // y ≠ 0}) (⌊max C 0⌋₊ + 2)
  have hC : C < (F.card : ℝ) := by
    rw [hF]
    push_cast
    have : C ≤ max C 0 := le_max_left C 0
    have : max C 0 < (⌊max C 0⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (max C 0)
    linarith
  have h_cont : Continuous (fun s : ℝ => ∑ y ∈ F, Real.exp (-Real.pi * s ^ 2 * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
    fun_prop
  have h_at_zero : (∑ y ∈ F, Real.exp (-Real.pi * (0 : ℝ) ^ 2 * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2)) = F.card := by
    simp
  have h_ev : ∀ᶠ s in 𝓝 (0 : ℝ), C < ∑ y ∈ F, Real.exp (-Real.pi * s ^ 2 * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    have := h_cont.tendsto 0
    rw [h_at_zero] at this
    exact this.eventually (Ioi_mem_nhds hC)
  filter_upwards [nhdsWithin_le_nhds h_ev, self_mem_nhdsWithin] with s hs hs_pos
  have hs' : 0 < s := hs_pos
  refine hs.le.trans ?_
  unfold rhoDualNonzero
  have h_sum_eq : (∑ y ∈ F, Real.exp (-Real.pi * s ^ 2 * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2)) =
      ∑ y ∈ F, rho (1 / s) ((y : dual L) : EuclideanSpace ℝ (Fin n)) := by
    refine Finset.sum_congr rfl (fun y _ => (rho_one_div s _).symm)
  rw [h_sum_eq]
  exact Summable.sum_le_tsum F (fun y _ => by unfold rho; positivity) (summable_rho_dual L hs')

private lemma tendsto_atTop_rhoDualNonzero {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Tendsto (fun s : ℝ => rhoDualNonzero (1 / s) L) atTop (𝓝 0) := by
  unfold rhoDualNonzero
  rw [show (0 : ℝ) = ∑' (_ : {y : dual L // y ≠ 0}), (0 : ℝ) by simp]
  refine tendsto_tsum_of_dominated_convergence (summable_dualBound L 1) (fun y => ?_) ?_
  · simp_rw [rho_one_div]
    rw [Real.tendsto_exp_comp_nhds_zero]
    have hy : 0 < Real.pi * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      have : ((y : dual L) : EuclideanSpace ℝ (Fin n)) ≠ 0 := Submodule.coe_eq_zero.not.mpr y.2
      positivity
    have h1 : Tendsto (fun s : ℝ => s ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_id
    have h2 : Tendsto (fun s : ℝ => s ^ 2 * (Real.pi * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2)) atTop atTop :=
      Tendsto.atTop_mul_const hy h1
    have h3 : Tendsto (fun s : ℝ => -(s ^ 2 * (Real.pi * ‖((y : dual L) : EuclideanSpace ℝ (Fin n))‖ ^ 2))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h2
    refine h3.congr (fun s => by ring)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs y
    exact rho_le_dualBound L zero_lt_one hs y

theorem solution {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ContinuousOn (fun s : ℝ => rhoDualNonzero (1 / s) L) (Set.Ioi 0) ∧
    StrictAntiOn (fun s : ℝ => rhoDualNonzero (1 / s) L) (Set.Ioi 0) ∧
    Tendsto (fun s : ℝ => rhoDualNonzero (1 / s) L) (𝓝[>] 0) atTop ∧
    Tendsto (fun s : ℝ => rhoDualNonzero (1 / s) L) atTop (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε →
      0 < smoothingParam L ε ∧ rhoDualNonzero (1 / smoothingParam L ε) L = ε := by
  have hcont := continuousOn_rhoDualNonzero L
  have hanti := strictAntiOn_rhoDualNonzero hn L
  have h0 := tendsto_zero_rhoDualNonzero hn L
  have hatTop := tendsto_atTop_rhoDualNonzero L
  refine ⟨hcont, hanti, h0, hatTop, fun ε hε => ?_⟩
  set f := fun s : ℝ => rhoDualNonzero (1 / s) L
  have h_ex_a : ∃ a > 0, ε ≤ f a := by
    have h_ev := (tendsto_atTop.mp h0 ε).and self_mem_nhdsWithin
    obtain ⟨a, ha1, ha2⟩ := h_ev.exists
    exact ⟨a, ha2, ha1⟩
  obtain ⟨a, ha_pos, ha_le⟩ := h_ex_a
  have h_ex_b : ∃ b, a ≤ b ∧ f b ≤ ε := by
    have h_ev1 : ∀ᶠ b in atTop, f b < ε := hatTop.eventually (gt_mem_nhds hε)
    have h_ev2 : ∀ᶠ b in atTop, a ≤ b := eventually_ge_atTop a
    obtain ⟨b, hb1, hb2⟩ := (h_ev1.and h_ev2).exists
    exact ⟨b, hb2, hb1.le⟩
  obtain ⟨b, hab, hb_le⟩ := h_ex_b
  have h_iv : ε ∈ f '' Set.Icc a b := by
    refine intermediate_value_Icc' hab (hcont.mono ?_) ⟨hb_le, ha_le⟩
    intro x hx
    exact Set.mem_Ioi.mpr (ha_pos.trans_le hx.1)
  obtain ⟨s₀, hs₀_mem, hs₀_eq⟩ := h_iv
  have hs₀_pos : 0 < s₀ := ha_pos.trans_le hs₀_mem.1
  have h_set_eq : {s : ℝ | 0 < s ∧ f s ≤ ε} = Set.Ici s₀ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · rintro ⟨hs_pos, hfs⟩
      rw [← hs₀_eq] at hfs
      exact (hanti.le_iff_ge hs_pos hs₀_pos).mp hfs
    · intro hs
      have hs_pos : 0 < s := hs₀_pos.trans_le hs
      refine ⟨hs_pos, ?_⟩
      rw [← hs₀_eq]
      exact (hanti.le_iff_ge hs_pos hs₀_pos).mpr hs
  have h_sp : smoothingParam L ε = s₀ := by
    unfold smoothingParam
    change sInf {s : ℝ | 0 < s ∧ f s ≤ ε} = s₀
    rw [h_set_eq, csInf_Ici]
  rw [h_sp]
  exact ⟨hs₀_pos, hs₀_eq⟩
