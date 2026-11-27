-- Prove2me | solution 1 for UpperTheory.Small.image_mem_Kur_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:33:27.632529+00:00
-- url     : https://prove2.me/submissions/94e1567f-603c-43e9-97b8-b713fa34ab93

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ZmodTwoQuadraticNeZero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_image_mem_of_roots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Small
theorem _root_.solution {l : ℕ} [Fact l.Prime] (J : H.E →+* Om l) {s : ℕ} (hs : H.condN.factorization l ≤ s) (x : H.E) :
    J x ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by
  have hl : l.Prime := Fact.out
  have hN := H.toHostRaw.condN_ne_zero
  refine H.toHostRaw.image_mem_of_roots J
    (MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}).toSubfield (fun y hy => ?_) x
  set a := l ^ H.condN.factorization l with ha
  set b := H.condN / a with hb
  have hab : a * b = H.condN := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hco : Nat.Coprime a b := (Nat.coprime_ordCompl hl hN).pow_left _
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hy
    exact zero_ne_one hy
  have hbez := Nat.gcd_eq_gcd_ab a b
  rw [hco.gcd_eq_one] at hbez
  have e : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hy0, ← hbez]
    simp
  have h1 : y ^ a ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _
    ⟨b, Nat.ordCompl_pos l hN, Nat.not_dvd_ordCompl hl hN, by rw [← pow_mul, hab, hy]⟩
  have h2 : y ^ b ∈ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by
    refine IntermediateField.subset_adjoin _ _ ?_
    obtain ⟨c, hc⟩ := pow_dvd_pow l hs
    show (y ^ b) ^ (l ^ s) = 1
    rw [hc, ← ha, ← pow_mul, ← mul_assoc, mul_comm b a, hab, pow_mul, hy, one_pow]
  show y ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}
  rw [e]
  exact mul_mem (zpow_mem ((le_sup_left : MaximalUnramifiedExtension l ≤ _) h1) _)
    (zpow_mem ((le_sup_right : IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} ≤ _) h2) _)
end UpperTheory.Small
