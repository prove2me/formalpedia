-- Prove2me | solution 1 for UpperTheory.HF.imgOne_gcd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:55.291811+00:00
-- url     : https://prove2.me/submissions/fe8384e3-14d5-4535-b951-1127640a1f83

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_ImgOneGcd
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_HC_Der_Rd_KK_gcd
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_imgOne_anti
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_imgOne


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
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ H.condN → g ∣ H.condN → H.imgOne (Nat.gcd f g) = H.imgOne f ⊔ H.imgOne g := by
  intro φ H f g hf hg
  have hgcd : Nat.gcd f g ∣ H.condN := (Nat.gcd_dvd_left f g).trans hf
  apply le_antisymm
  · rintro x hx
    rw [H.mem_imgOne hgcd] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have key := Der.Rd.KK_gcd (N := H.condN) ((H.imgOne f ⊔ H.imgOne g).comap H.art) hf hg
      (fun v hv => Subgroup.mem_sup_left ((H.mem_imgOne hf _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      (fun v hv => Subgroup.mem_sup_right ((H.mem_imgOne hg _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      u (Der.Rd.mem_KK.2 hu)
    exact key
  · exact sup_le (H.imgOne_anti (Nat.gcd_dvd_left f g) hf) (H.imgOne_anti (Nat.gcd_dvd_right f g) hg)
end UpperTheory.HF
