-- Prove2me | solution 1 for ThreeSum1960614.FixedModel.bound_of_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T13:34:51.103771+00:00
-- url     : https://prove2.me/submissions/8379cd5c-65b6-4bc5-bd3a-2bbecbec833e

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_FixedModelAlgebra
import Definitions.Def_ThreeSum1960614_ModelWitnessPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
namespace ThreeSum1960614.FixedModel















end ThreeSum1960614.FixedModel

end

open ThreeSum1960614 ThreeSum1960614.FixedModel in
/-- Four necessary charges suffice; the point witnesses remain explicit premises. -/
theorem solution (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R)
    (hE : e0 ≤ E 232) (hk : k0 ≤ kappa 232) (hrho : ratio0 ≤ ratio)
    (hgamma : th ≤ split → gamma 232 th ≤ gammaCap)
    (hentropy : split ≤ th → entropyFloor ≤ entropy th) : lowerTarget < R := by
  rcases hmodel with ⟨he,_,hb,hS,_,_,_,_,_,hswitch,_,hcost⟩
  by_cases hR : 2 ≤ R
  · exact lt_of_lt_of_le (by norm_num [lowerTarget]) hR
  let delta : ℝ := 2-R
  have hbox : 2-e*S ≤ R := hcost _ (by simp [ledger])
  have henc : 1+e*(E 232-b) ≤ R := hcost _ (by simp [ledger])
  have hini : 2-e*(1/2+b-entropy th) ≤ R := hcost _ (by simp [ledger])
  have hrec : 2-e*(1/2-b-kappa 232-ratio*(1+S-2*b)) ≤ R :=
    hcost _ (by simp [ledger])
  have hEscale := mul_le_mul_of_nonneg_left hE he.le
  have hkscale := mul_le_mul_of_nonneg_left hk he.le
  have hrscale := mul_le_mul_of_nonneg_left hrho
    (mul_nonneg he.le (show 0 ≤ 1+S-2*b by linarith only [hS,hb]))
  have hbs : (1+ratio0)*delta+a*(e*b) ≤ A*e := by
    dsimp [delta,a,A,ratio0]
    dsimp [ratio0] at hrscale
    nlinarith only [hbox,hrec,hkscale,hrscale]
  have hapos : 0 < a := by norm_num [a,ratio0]
  have hswitchScale := mul_le_mul_of_nonneg_left hswitch he.le
  have hsave : delta ≤ savingCap*e := by
    rcases le_total th split with hleft | hright
    · have hgscale := mul_le_mul_of_nonneg_left (hgamma hleft) he.le
      have hswitchDelta : delta-2*e*b ≤ e*gammaCap := by
        dsimp [delta]
        nlinarith only [hbox,hswitchScale,hgscale]
      have hs := mul_le_mul_of_nonneg_left hswitchDelta hapos.le
      have hcombine : 3*delta ≤ (2*A+a*gammaCap)*e := by
        dsimp [a,A,ratio0] at hbs hs ⊢
        nlinarith only [hbs,hs]
      have hcap : 2*A+a*gammaCap ≤ 3*savingCap := by
        norm_num [A,a,ratio0,k0,gammaCap,savingCap]
      have hcapScale := mul_le_mul_of_nonneg_right hcap he.le
      nlinarith only [hcombine,hcapScale]
    · have hhscale := mul_le_mul_of_nonneg_left (hentropy hright) he.le
      have hinitDelta : delta ≤ e/2+e*b-e*entropyFloor := by
        dsimp [delta]
        nlinarith only [hini,hhscale]
      have hs := mul_le_mul_of_nonneg_left hinitDelta hapos.le
      have hcombine : (2-ratio0)*delta ≤
          (1-2*ratio0-k0-a*entropyFloor)*e := by
        dsimp [a,A,ratio0] at hbs hs ⊢
        nlinarith only [hbs,hs]
      have hcap : 1-2*ratio0-k0-a*entropyFloor ≤ (2-ratio0)*savingCap := by
        norm_num [a,ratio0,k0,entropyFloor,savingCap]
      have hcapScale := mul_le_mul_of_nonneg_right hcap he.le
      have hden : 0 < 2-ratio0 := by norm_num [ratio0]
      norm_num [ratio0] at hcombine hcapScale ⊢
      nlinarith only [hcombine,hcapScale]
  have henc0 : e*(e0-b)+delta ≤ 1 := by
    dsimp [delta]
    nlinarith only [henc,hEscale]
  have hsenc := mul_le_mul_of_nonneg_left henc0 hapos.le
  have hbudget : C*e+(2-ratio0)*delta ≤ a := by
    dsimp [C,A,a,ratio0] at hsenc hbs ⊢
    nlinarith only [hsenc,hbs]
  have hC : 0 < C := by norm_num [C,a,A,ratio0,e0,k0]
  have hU : 0 < savingCap := by norm_num [savingCap]
  have hsaveC := mul_le_mul_of_nonneg_left hsave hC.le
  have hbudgetU := mul_le_mul_of_nonneg_left hbudget hU.le
  have hfinal : (C+(2-ratio0)*savingCap)*delta ≤ a*savingCap := by
    nlinarith only [hsaveC,hbudgetU]
  have hstrict : a*savingCap < (C+(2-ratio0)*savingCap)*(2-lowerTarget) := by
    norm_num [C,a,A,ratio0,e0,k0,savingCap,lowerTarget]
  have hden : 0 < C+(2-ratio0)*savingCap := by
    norm_num [C,a,A,ratio0,e0,k0,savingCap]
  dsimp [delta] at hfinal
  norm_num [C,a,A,ratio0,e0,k0,savingCap,lowerTarget] at hfinal ⊢
  linarith only [hfinal]

#print axioms solution
