-- Prove2me | solution 1 for UpperTheory.HF.rho_art
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:59:48.225522+00:00
-- url     : https://prove2.me/submissions/889528c6-beea-4efb-8273-6aee24c19e84

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RhoArt
import Theorems.Thm_Formalism_HC_Der_Rd_card_KK
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
import Theorems.Thm_Formalism_HC_Der_Rd_rho_eq
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_unitsOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostRaw φ) {f : ℕ}, f ∣ H.condN → Formalism.HC.Der.Rd.rho H.art.ker f = 1 - 1 / (Nat.card (H.imgOne f) : ℝ) := by
  intro φ H f hf
  classical
  rw [Formalism.HC.Der.Rd.rho_eq _ hf]
  have h1 := (H.art.ker.subgroupOf (H.unitsOne f)).card_mul_index
  have h2 : (H.art.ker.subgroupOf (H.unitsOne f)).index = Nat.card (H.imgOne f) :=
    Subgroup.relIndex_ker (H.unitsOne f) H.art
  have h3 : Nat.card (H.unitsOne f) = (Formalism.HC.Der.Rd.KK H.condN f).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf])
  have h4 : Nat.card (H.art.ker.subgroupOf (H.unitsOne f)) =
      ((Formalism.HC.Der.Rd.KK H.condN f).filter fun u => u ∈ H.art.ker).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun u => u ∈ H.unitsOne f)
      (fun u => u ∈ H.art.ker)).trans (Equiv.subtypeEquivRight fun u => ?_))
    rw [Finset.mem_filter, Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf]
  rw [h2, h3, h4] at h1
  have h5 := Formalism.HC.Der.Rd.card_KK hf
  rw [← h1] at h5
  have h6 := congrArg (Nat.cast : ℕ → ℝ) h5
  push_cast at h6
  have hN : (H.condN.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos H.condN)).ne'
  have hI : (Nat.card (H.imgOne f) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  congr 1
  rw [div_eq_div_iff hN hI, one_mul, ← h6]
  rw [mul_right_comm]
  congr!
end UpperTheory.HF
