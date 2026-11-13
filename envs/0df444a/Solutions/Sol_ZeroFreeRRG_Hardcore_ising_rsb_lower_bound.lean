-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.ising_rsb_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:13:56.886852+00:00
-- url     : https://prove2.me/submissions/80b6fe3f-614b-45ee-9644-1b977249f94d

import Theorems.Thm_ZeroFreeRRG_Hardcore_weak_ks_from_variational
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds
open scoped Classical
open ZeroFreeRRG.Hardcore

private theorem beta_nonneg (d q : ℕ) : 0 ≤ betaRSB d q := by
  unfold betaRSB
  split_ifs with he
  · exact le_rfl
  · have hne : (pottsWitness d q).Nonempty := Set.nonempty_iff_ne_empty.mpr he
    obtain ⟨x,hx⟩ := hne
    have hb : BddAbove (pottsWitness d q) := ⟨1, fun y hy => hy.2.1.le⟩
    exact le_trans hx.1.le (le_csSup hb hx)

/-- The fourth-order variational test forces the Ising RSB threshold to be at least KS. -/
theorem solution (d : ℕ) (hd : 3 ≤ d) :
    (Real.sqrt ((d : ℝ) - 1) - 1) / (Real.sqrt ((d : ℝ) - 1) + 1) ≤ betaRSB d 2 := by
  by_contra hn
  have hlt : betaRSB d 2 < (Real.sqrt ((d : ℝ) - 1) - 1) /
      (Real.sqrt ((d : ℝ) - 1) + 1) := lt_of_not_ge hn
  let s : ℝ := Real.sqrt ((d:ℝ)-1)
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = (d:ℝ)-1 := by dsimp [s]; rw [Real.sq_sqrt (by linarith)]
  have hs1 : 1 < s := by nlinarith
  let t : ℝ := (s-1)/(s+1)
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    apply (div_lt_one (by linarith : 0 < s+1)).2
    linarith
  have hbt : betaRSB d 2 < t := hlt
  let β : ℝ := (betaRSB d 2 + t)/2
  have hb0 : 0 < β := by dsimp [β]; linarith [beta_nonneg d 2]
  have hb1 : β < 1 := by dsimp [β]; linarith
  have hbt' : betaRSB d 2 < β := by dsimp [β]; linarith
  have hβt : β < t := by dsimp [β]; linarith
  have hfactor : 1+β < s*(1-β) := by
    have hh : β * (s+1) < s-1 := (lt_div_iff₀ (by linarith : 0 < s+1)).mp hβt
    nlinarith
  have hp : 0 < 1-β := by linarith
  have hp' : 0 < 1+β := by linarith
  have hsq' : (1+β)^2 < ((d:ℝ)-1)*(1-β)^2 := by
    nlinarith [sq_nonneg (s*(1-β) - (1+β))]
  have hgt : 1 < ((d:ℝ)-1)*((1-β)/(1+β))^2 := by
    have heq : ((d:ℝ)-1)*((1-β)/(1+β))^2 =
        (((d:ℝ)-1)*(1-β)^2)/(1+β)^2 := by rw [div_pow]; ring
    rw [heq]
    apply (lt_div_iff₀ (sq_pos_of_pos hp')).2
    simpa using hsq'
  have hnrs : ¬ VariationalRS (.potts 2) d β := by
    intro hrs
    have hweak := (weak_ks_from_variational d 2 hd (by norm_num)).2 β hb0.le hb1 hrs
    norm_num at hweak
    linarith
  have hw : β ∈ pottsWitness d 2 := by
    refine ⟨hb0,hb1,?_⟩
    simpa [VariationalRS, not_forall, not_le] using hnrs
  have hbdd : BddAbove (pottsWitness d 2) := ⟨1,fun x hx => hx.2.1.le⟩
  have hle : β ≤ betaRSB d 2 := by
    unfold betaRSB
    rw [if_neg (Set.nonempty_iff_ne_empty.mp ⟨β,hw⟩)]
    exact le_csSup hbdd hw
  linarith
