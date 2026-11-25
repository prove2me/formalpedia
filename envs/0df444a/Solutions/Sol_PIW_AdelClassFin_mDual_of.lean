-- Prove2me | solution 1 for PIW.AdelClassFin.mDual_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:42.517608+00:00
-- url     : https://prove2.me/submissions/169caa97-08b7-404b-ab2b-38b63d97332b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop
import Theorems.Thm_PIW_AdelClassFin_dictTop_mul_inv
import Theorems.Thm_PIW_AdelClassFin_dictTop_hhat_unit
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


section
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
private theorem sigR_inclE' (I : AutInst) (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) :=
  Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) e 1
private theorem inclE_hform (I : AutInst) (w v : Fin I.n → I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J w v) =
      hhat I (iv I w) (iv I v) := by
  unfold hhat iv
  simp only [Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, sigR_inclE']
private theorem sigR_mem_intAf (I : AutInst) (c : I.E ⊗[I.F] Af I.F) (hc : c ∈ IntAf I.F I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) c ∈ IntAf I.F I.E := by
  have hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := he
      show Formalism.UG.sigR I.cm.sig (Af I.F)
        (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E o)) ∈ IntAf I.F I.E
      rw [sigR_inclE']
      have hs : starRingEnd I.E (algebraMap (𝓞 I.E) I.E o) ∈ Formalism.UG.intOE I.E :=
        ⟨⟨star (o : I.E),
          (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩
      exact Subring.subset_closure (Or.inl ⟨⟨_, hs⟩, rfl⟩)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) ∈ IntAf I.F I.E
      have h1 := Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) (1 : I.E) a
      rw [map_one] at h1
      have e1 : Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) = (1 : I.E) ⊗ₜ[I.F] a := h1
      rw [e1]
      exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact hle hc
private theorem hhat_zero_left' (I : AutInst) (z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I 0 z = 0 := by
  simp [hhat, Formalism.UG.hform]
private theorem hhat_add_left' (I : AutInst) (a b z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (a + b) z = hhat I a z + hhat I b z := by
  simp only [hhat, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
private theorem hhat_smul_left' (I : AutInst) (r : I.E ⊗[I.F] Af I.F)
    (a z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (r • a) z = Formalism.UG.sigR I.cm.sig (Af I.F) r * hhat I a z := by
  simp only [hhat, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
end PIW.AdelClassFin
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (hDI : DInter) (hLI : LHatInt) (hLD : LHatDual) (hG : MGen) : MDual := by
  intro I x v
  constructor
  · intro hv w hw
    apply hDI I.F I.E
    rw [inclE_hform, ← dictTop_hhat_unit I x⁻¹]
    exact hLI I (I.fmat x⁻¹ *ᵥ iv I w) hw (I.fmat x⁻¹ *ᵥ iv I v) hv
  · intro hv
    show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf
    apply hLD I
    intro y hy
    rw [← dictTop_hhat_unit I x y, Matrix.mulVec_mulVec, dictTop_mul_inv, Matrix.one_mulVec]
    refine Submodule.span_induction (p := fun z _ => hhat I z (iv I v) ∈ IntAf I.F I.E)
      (fun z hz => ?_) ?_ (fun z w _ _ hz hw => ?_) (fun c z _ hz => ?_) (hG I x y hy)
    · obtain ⟨w, rfl⟩ := hz
      obtain ⟨o, ho⟩ := hv w w.2
      rw [← inclE_hform, ← ho]
      exact Subring.subset_closure (Or.inl ⟨⟨(o : I.E), o, rfl⟩, rfl⟩)
    · rw [hhat_zero_left']
      exact (IntAf I.F I.E).zero_mem
    · rw [hhat_add_left']
      exact (IntAf I.F I.E).add_mem hz hw
    · show hhat I ((c : I.E ⊗[I.F] Af I.F) • z) (iv I v) ∈ IntAf I.F I.E
      rw [hhat_smul_left']
      exact (IntAf I.F I.E).mul_mem (sigR_mem_intAf I _ c.2) hz
end PIW.AdelClassFin
