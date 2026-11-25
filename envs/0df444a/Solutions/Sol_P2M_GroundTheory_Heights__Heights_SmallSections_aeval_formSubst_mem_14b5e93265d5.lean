-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_aeval_formSubst_mem_14b5e93265d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:37.989541+00:00
-- url     : https://prove2.me/submissions/45f8fdb4-0daa-49a2-ace3-519093513835

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : f ∈ D.extIdeal) : aeval (formSubst D g c) f ∈ P.ideal := by
  let ψ : MvPolynomial (Option ι) P.FunField →+* P.FunField :=
    eval fun o ↦ o.elim (P.mkF (chartMonomial c d)) fun _ ↦ 1
  have hid : P.mkF.comp (aeval (formSubst D g c)).toRingHom = ψ.comp D.extMap := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun v ↦ ?_)
    · simp [AddBlockData.extMap]
    · obtain ⟨o, i⟩ := v
      cases o with
      | none =>
        simp [AddBlockData.extMap, AddBlockData.extVal, formSubst, ψ, hg.value c hc i, mul_comm]
      | some k =>
        simp [AddBlockData.extMap, AddBlockData.extVal, formSubst, ψ]
  rw [← P.mkF_eq_zero_iff]
  have h := congrArg (fun φ ↦ φ f) hid
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
  rw [h, (RingHom.mem_ker).mp hf, map_zero]
end GroundTheory.Heights₂.Heights.SmallSections
