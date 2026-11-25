-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.exists_short_vectors_realSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:08.786478+00:00
-- url     : https://prove2.me/submissions/8b30d12c-20f6-46e1-abf8-349c2fd63ff2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_add__6da13cd7e94f
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zero__c975529e773e
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zsmul__b8e6a11e43d5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_eq_zero_of_im_L
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_mem_L_of_int
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_exists_isU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_mem_IR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_one_le_abs_im
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sq_le_Qy_of_le_firstMinimum
import Theorems.Thm_transference_successive_minima
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hsat : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) (hla : 0 < X.la1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧
      LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ Module.finrank ℝ (IR I) / X.la1 + ε := by
  set K := IR I with hK
  set N := Module.finrank ℝ K with hNdef
  let e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ K).repr
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin N)) :=
    { carrier := {z | ∃ y ∈ X.L, IsU I y ((e.symm z : K) : Vsp X.dim)}
      add_mem' := by
        rintro z z' ⟨y, hy, hu⟩ ⟨y', hy', hu'⟩
        exact ⟨y + y', X.L.add_mem hy hy', by simpa using hu.add' hu'⟩
      zero_mem' := ⟨0, X.L.zero_mem, by simpa using IsU.zero' I⟩
      smul_mem' := by
        rintro k z ⟨y, hy, hu⟩
        exact ⟨k • y, X.L.smul_mem k hy, by simpa using hu.zsmul' k⟩ }
  have hmemM : ∀ y ∈ X.L, ∀ u, IsU I y u → ∃ z ∈ M, ((e.symm z : K) : Vsp X.dim) = u :=
    fun y hy u hu => ⟨e ⟨u, hu.1⟩, ⟨y, hy, by simpa using hu⟩, by simp⟩
  have hinner : ∀ z z' : EuclideanSpace ℝ (Fin N),
      ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : Vsp X.dim), ((e.symm z' : K) : Vsp X.dim)⟫_ℝ := by
    intro z z'
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  have hnormE : ∀ z, ‖((e.symm z : K) : Vsp X.dim)‖ = ‖z‖ := by
    intro z
    rw [← e.symm.norm_map z]
    rfl
  have hdual : ∀ z ∈ PI.dualZ M, ((e.symm z : K) : Vsp X.dim) ∈ I := by
    intro z hz
    apply hsat _ ?_ (e.symm z).2
    apply mem_L_of_int X
    intro y hy
    obtain ⟨u, hu⟩ := exists_isU I y
    obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
    obtain ⟨k, hk⟩ := hz z' hz'M
    refine ⟨k, ?_⟩
    rw [← hu.2 _ (e.symm z).2, ← hk, hinner, hz', real_inner_comm]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have : IsEmpty (Fin N) := by rw [hN0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  obtain ⟨a0, ha0I, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hK0 : K = ⊥ := by
      rw [eq_bot_iff, hK]
      exact Submodule.span_le.2 (fun a ha => by simp [hcon a ha])
    have : N = 0 := by rw [hNdef, hK0]; exact finrank_bot ℝ _
    omega
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ z' ∈ M, ⟪z', z⟫_ℝ = 0 := fun z' hz' =>
      (Submodule.mem_orthogonal _ _).1 hz z' (Submodule.subset_span hz')
    have ha : ((e.symm z : K) : Vsp X.dim) = 0 := by
      apply eq_zero_of_im_L X
      intro y hy
      obtain ⟨u, hu⟩ := exists_isU I y
      obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
      rw [← hu.2 _ (e.symm z).2, ← hz', ← hinner]
      exact h0 z' hz'M
    have : e.symm z = 0 := Subtype.ext ha
    simpa using congrArg e this

  obtain ⟨s, hsI, hsspan, hsli⟩ := exists_linearIndependent ℝ (I : Set (Vsp X.dim))
  have hsfin : s.Finite := hsli.setFinite
  set A := ∑ a ∈ hsfin.toFinset, ‖a‖ + 1 with hA
  have hApos : 0 < A := by
    have : 0 ≤ ∑ a ∈ hsfin.toFinset, ‖a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hlow : ∀ z ∈ M, z ≠ 0 → 1 / A ≤ ‖z‖ := by
    intro z hzM hz0
    obtain ⟨y, hy, hu⟩ := hzM
    set u := ((e.symm z : K) : Vsp X.dim)
    have hu0 : u ≠ 0 := by
      intro h0
      apply hz0
      have : e.symm z = 0 := Subtype.ext h0
      simpa using congrArg e this
    obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ⟪u, a⟫_ℝ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : ∀ w ∈ Submodule.span ℝ s, ⟪u, w⟫_ℝ = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx => exact hcon x hx
        | zero => exact inner_zero_right _
        | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
        | smul r x _ hx => rw [real_inner_smul_right, hx, mul_zero]
      have h1 := this u (by rw [hsspan]; exact hu.1)
      exact hu0 (inner_self_eq_zero.1 h1)
    have h1 : 1 ≤ |⟪u, a⟫_ℝ| := by
      rw [hu.2 a (mem_IR (hsI has))]
      rw [hu.2 a (mem_IR (hsI has))] at ha
      exact one_le_abs_im X hy (hle (hsI has)) ha
    have h2 : |⟪u, a⟫_ℝ| ≤ ‖u‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h3 : ‖a‖ ≤ A := by
      have := Finset.single_le_sum (f := fun a => ‖a‖) (fun _ _ => norm_nonneg _)
        ((Set.Finite.mem_toFinset hsfin).2 has)
      linarith
    rw [← hnormE z, div_le_iff₀ hApos]
    nlinarith [norm_nonneg u]
  have hdisc : DiscreteTopology M := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    refine ⟨1 / A, by positivity, fun z hz => ?_⟩
    by_contra hz0
    have h1 := hlow z z.2 (fun h => hz0 (Subtype.ext h))
    rw [dist_zero_right] at hz
    have : ‖(z : EuclideanSpace ℝ (Fin N))‖ = ‖z‖ := rfl
    linarith
  have hT := transference_successive_minima N M hdisc hspan N hNpos le_rfl
  rw [show N + 1 - N = 1 by omega] at hT
  have hsm0 : 0 ≤ PI.succMin M N := Real.sInf_nonneg (fun t ht => ht.1)
  have hdual1 : X.la1 ≤ PI.succMin (PI.dualZ M) 1 := by
    apply le_csInf
    · have hmem : e ⟨a0, mem_IR ha0I⟩ ∈ PI.dualZ M := by
        intro z hz
        obtain ⟨y, hy, hu⟩ := hz
        obtain ⟨k, hk⟩ := X.integral y a0 hy (hle ha0I)
        refine ⟨k, ?_⟩
        rw [hinner, LinearIsometryEquiv.symm_apply_apply, real_inner_comm, hu.2 a0 (mem_IR ha0I), hk]
      refine ⟨‖e ⟨a0, mem_IR ha0I⟩‖, norm_nonneg _, fun _ => e ⟨a0, mem_IR ha0I⟩,
        fun _ => hmem, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      intro h0
      apply ha0
      have := congrArg e.symm h0
      simpa using congrArg Subtype.val this
    · rintro t ⟨-, v, hvM, hvli, hvt⟩
      have hv0 := hvli.ne_zero 0
      have ha := hdual (v 0) (hvM 0)
      have hne : ((e.symm (v 0) : K) : Vsp X.dim) ≠ 0 := by
        intro h0
        apply hv0
        have : e.symm (v 0) = 0 := Subtype.ext h0
        simpa using congrArg e this
      calc X.la1 ≤ ‖((e.symm (v 0) : K) : Vsp X.dim)‖ := sq_le_Qy_of_le_firstMinimum X (hle ha) hne
        _ = ‖v 0‖ := hnormE _
        _ ≤ t := hvt 0
  have hlam : PI.succMin M N ≤ N / X.la1 := by
    rw [le_div_iff₀ hla]
    nlinarith

  have hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty := by
    obtain ⟨s', hs'M, hs'span, hs'li⟩ := exists_linearIndependent ℝ (M : Set (EuclideanSpace ℝ (Fin N)))
    have hfin' : s'.Finite := hs'li.setFinite
    have : Fintype s' := hfin'.fintype
    let bs := Module.Basis.mk hs'li (by rw [Subtype.range_coe, hs'span, hspan])
    have hcard : Fintype.card s' = N := by
      rw [← Module.finrank_eq_card_basis bs, finrank_euclideanSpace_fin]
    let eq : Fin N ≃ s' := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨∑ j, ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖,
      Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j => (eq j : EuclideanSpace ℝ (Fin N)),
      fun j => hs'M (eq j).2, hs'li.comp eq eq.injective, fun j => ?_⟩
    exact Finset.single_le_sum (f := fun j => ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (PI.succMin M N) hε)
  choose y hy hyU using hvM
  refine ⟨y, fun j => ((e.symm (v j) : K) : Vsp X.dim), fun j => ⟨hy j, hyU j⟩, ?_, ?_⟩
  · exact (hvli.map' e.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)).map' K.subtype
      K.ker_subtype
  · intro j
    rw [hnormE]
    have := hvt j
    have h2 : PI.succMin M N = sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t} := rfl
    linarith
end ReciprocityTheory.ChartRestriction.G.I2
