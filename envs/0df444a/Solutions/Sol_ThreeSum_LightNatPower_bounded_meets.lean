-- Prove2me | solution 1 for ThreeSum.LightNatPower.bounded_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:20.269684+00:00
-- url     : https://prove2.me/submissions/dea02d38-d84b-48e3-9dfb-17ad11b740ee

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac

set_option autoImplicit false
open ThreeSum ThreeSum.LightNatPower
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightNatPower
theorem _root_.solution {p b e : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hword : (((b+1)^(e+1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [b,e] μ (time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) := by
  apply meets hp μ he
  intro i hi
  have hbase := Nat.pow_le_pow_left (show b ≤ b+1 by omega) i
  have hexp : (b+1)^i ≤ (b+1)^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz : ((b^i : ℕ) : ℤ) ≤ (((b+1)^(e+1) : ℕ) : ℤ) := by
    exact_mod_cast hbase.trans hexp
  exact hz.trans hword
end ThreeSum.LightNatPower
