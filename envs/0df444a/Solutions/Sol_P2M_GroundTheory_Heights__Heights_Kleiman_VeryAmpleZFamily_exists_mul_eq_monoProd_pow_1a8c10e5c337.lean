-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_eq_monoProd_pow_1a8c10e5c337
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:42.831883+00:00
-- url     : https://prove2.me/submissions/a7c4d91f-297c-4e6e-ad78-ad5ba4df57f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_mem_monos_27cdb6de9abb


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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
theorem _root_.solution {T : Finset (Fin (r + 1))} {s : Poly S r} (hs : s ∈ monos T) :
    ∃ (k : ℕ) (t : Poly S r), t ∈ monos T ∧ s * t = AmpleAffineGen.monoProd T ^ k := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨1, AmpleAffineGen.monoProd (T.erase i),
      AmpleAffineGen.monoProd_mem_monos (Finset.erase_subset _ _), by
        rw [pow_one, AmpleAffineGen.monoProd, AmpleAffineGen.monoProd,
          Finset.mul_prod_erase _ _ (by exact_mod_cast hi)]⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, t, ht, e⟩ := ha
    obtain ⟨k', t', ht', e'⟩ := hb
    exact ⟨k + k', t * t', mul_mem ht ht', by
      rw [pow_add, ← e, ← e']; ring⟩
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
