-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814.movingCut_zero_of_helper_dvd_yukon_9979e66e9721
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T01:36:56.401603+00:00
-- url     : https://prove2.me/submissions/6613c2ac-0a53-4b0f-b719-1905a72132d5




import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceClearing6814_movingCut_value_yukon_ad183332c771
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_6031b066ec5b1f25736844be
import Definitions.Def_Yukon_91e99a7c9682f8cc19028ba7
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceClearing6814.movingCut_value := @ProximityPrize.SubmissionLower.MovingSourceClearing6814.movingCut_value_yukon_ad183332c771
namespace ProximityPrize.SubmissionLower.MovingSourceClearing6814
end MovingSourceClearing6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy
end SecondJetCarrierDichotomy
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetClearedHelper
end SecondJetClearedHelper
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetCoefficients
end SecondJetCoefficients
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN207
end RCN207
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
open MvPolynomial RCN136 RCN207 SecondJetCoefficients SecondJetClearedHelper
open SecondJetCarrierDichotomy MovingSourceClearing6814
variable {K E : Type*} [Field K] [Field E]
theorem _root_.solution {L : Type*} [Field L]
    (phi : Polynomial K →+* E) (ev : MvPolynomial (Fin 3) E →+* L)
    (P : WholeSpaceCube6814.Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (s : ℕ) (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hdiv : F ∣ helper P F s 0)
    (hF : ev (surfaceMap phi F)=0)
    (hH : ev (surfaceMap phi (2*RCN313.polyH K F))≠0)
    (quadratic A : MvPolynomial (Fin 3) E) (target : E)
    (hM : ev (movingEquation (surfaceMap phi (RCN313.polyH K F))
      (surfaceMap phi (RCN313.polyG K F)) quadratic A target)=0) :
    ev (movingCut phi P s quadratic A target)=0  := by
  let psi := ev.comp (surfaceMap phi)
  let H := surfaceMap phi (RCN313.polyH K F)
  let G := surfaceMap phi (RCN313.polyG K F)
  have hpsiF : psi F=0 := hF
  have hpsiH : psi (2*RCN313.polyH K F)≠0 := hH
  have hz := map_dvd psi hdiv
  rw [hpsiF,zero_dvd_iff] at hz
  have hmapped := mapped_helper P F psi s 0 hS hpsiH
  simp only [Nat.sub_zero,Function.iterate_zero,id_eq] at hmapped
  rw [hmapped] at hz
  have hroot := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero s hpsiH)
  have hden : psi (2*RCN313.polyH K F)=ev (2*H) := by
    simp only [psi,H,RingHom.comp_apply,map_mul,map_ofNat]
  have hHH : ev H≠0 := by
    intro hh
    apply hpsiH
    rw [hden,map_mul,hh,mul_zero]
  have hsigma : ev (2*H)*ratio psi F=ev G := by
    rw [←hden]
    change psi (2*RCN313.polyH K F)*ratio psi F=psi (RCN313.polyG K F)
    unfold ratio
    field_simp
  rw [movingCut_value phi ev P s hS H G quadratic A target (ratio psi F) hHH hM hsigma]
  exact mul_eq_zero_of_right _ hroot
end
end MovingSourceCarrierZeros6814
end SubmissionLower
end ProximityPrize
