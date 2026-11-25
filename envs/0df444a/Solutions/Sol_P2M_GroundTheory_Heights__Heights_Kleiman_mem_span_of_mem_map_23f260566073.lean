-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_span_of_mem_map_23f260566073
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:28.728894+00:00
-- url     : https://prove2.me/submissions/5f7d8623-0c60-4e65-b149-8e1bb0361e6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (qq : Ideal (Poly S N)) {f : Poly F N}
    (hf : f ∈ qq.map (MvPolynomial.map (algebraMap S F))) :
    f ∈ Submodule.span F (MvPolynomial.map (algebraMap S F) '' (qq : Set (Poly S N))) := by
  set T := Submodule.span F (MvPolynomial.map (algebraMap S F) '' (qq : Set (Poly S N)))
  have hX : ∀ (i : Fin (N + 1)) (g : Poly F N), g ∈ T → X i * g ∈ T := fun i g hg => by
    refine Submodule.span_induction (p := fun g _ => X i * g ∈ T) ?_
      (by rw [mul_zero]; exact T.zero_mem)
      (fun a b _ _ ha hb => by rw [mul_add]; exact T.add_mem ha hb)
      (fun c g _ hg => by rw [mul_smul_comm]; exact T.smul_mem c hg) hg
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.subset_span ⟨X i * p, qq.mul_mem_left _ hp, by rw [map_mul, map_X]⟩
  have hmul : ∀ (c g : Poly F N), g ∈ T → c * g ∈ T := fun c => by
    induction c using MvPolynomial.induction_on with
    | C a => intro g hg; rw [← smul_eq_C_mul]; exact T.smul_mem a hg
    | add p q hp hq => intro g hg; rw [add_mul]; exact T.add_mem (hp g hg) (hq g hg)
    | mul_X p i hp => intro g hg; rw [mul_assoc]; exact hp _ (hX i g hg)
  refine Submodule.span_induction (p := fun g _ => g ∈ T) (fun g hg => Submodule.subset_span hg)
    T.zero_mem (fun a b _ _ ha hb => T.add_mem ha hb) (fun c g _ hg => hmul c g hg) hf
end GroundTheory.Heights₂.Heights.Kleiman
