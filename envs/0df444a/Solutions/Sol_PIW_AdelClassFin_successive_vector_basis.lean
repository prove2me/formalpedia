-- Prove2me | solution 1 for PIW.AdelClassFin.successive_vector_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:36.633904+00:00
-- url     : https://prove2.me/submissions/c86c6e73-030f-479b-9ddc-cffb60c05542

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorBasis
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField
namespace PIW.AdelClassFin
theorem _root_.solution : SvBasis := by
  intro E _ _ m M hfg hspan
  classical
  let M' : Submodule ℤ (Fin m → E) := M.restrictScalars ℤ
  have hfg' : M'.FG := hfg.restrictScalars
  have : Module.Finite ℤ M' := Module.Finite.iff_fg.2 hfg'
  have : Module.Free ℤ M' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ M'
  let e0 : Module.Free.ChooseBasisIndex ℤ M' → Fin m → E := fun i => (b i : Fin m → E)
  have hli : LinearIndependent ℤ e0 := b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ e0 := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hrep : ∀ x (hx : x ∈ M), x = ∑ i, (b.repr ⟨x, hx⟩ i) • e0 i := by
    intro x hx
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : M')).symm
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul] using h1
  have hmemM : ∀ x ∈ M, x ∈ Submodule.span ℚ (Set.range e0) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstab : ∀ c : E, ∀ v ∈ Submodule.span ℚ (Set.range e0), c • v ∈ Submodule.span ℚ (Set.range e0) := by
    intro c v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
      let α : 𝓞 E := ⟨y • c, hyi⟩
      have hαv : α • e0 i ∈ M := M.smul_mem α (b i).2
      have hyQ : (y : ℚ) ≠ 0 := Int.cast_ne_zero.2 hy0
      have : c • e0 i = ((y : ℚ)⁻¹) • (α • e0 i) := by
        have hα : (α • e0 i) = ((y : E) * c) • e0 i := by
          rw [Algebra.smul_def (A := E)] at *
          show ((y • c : E)) • e0 i = _
          rw [zsmul_eq_mul]
        rw [hα, mul_smul, ← smul_assoc]
        rw [show ((y : ℚ)⁻¹ • ((y : E))) = (1 : E) by
          rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel₀ (Int.cast_ne_zero.2 hy0)]]
        rw [one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (hmemM _ hαv)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  have hspanQ : Submodule.span ℚ (Set.range e0) = ⊤ := by
    let W : Submodule E (Fin m → E) :=
      { toAddSubmonoid := (Submodule.span ℚ (Set.range e0)).toAddSubmonoid
        smul_mem' := fun c v hv => hstab c v hv }
    have hle : Submodule.span E (M : Set (Fin m → E)) ≤ W := Submodule.span_le.2 fun x hx => hmemM x hx
    rw [hspan] at hle
    rw [eq_top_iff]
    intro v _
    exact hle (Submodule.mem_top)
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M') ℚ (Fin m → E) :=
    Module.Basis.mk hliQ (by rw [hspanQ])
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M') = m * Module.finrank ℚ E := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi_fintype]
    simp
  let σ : Fin (m * Module.finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ M' := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e0 ∘ σ, hliQ.comp σ σ.injective, fun i => (b (σ i)).2, fun x hx => ?_⟩
  refine ⟨fun i => b.repr ⟨x, hx⟩ (σ i), ?_⟩
  conv_lhs => rw [hrep x hx]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  rfl
end PIW.AdelClassFin
