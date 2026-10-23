-- Prove2me | solution 1 for RobustFPA.VarBid.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T03:52:42.220827+00:00
-- url     : https://prove2.me/submissions/92d49885-04c5-4efd-bd0e-de5513aa98c5

import Definitions.Def_RobustFPA_VarBid_Model
import Definitions.Def_RobustFPA_VarBid_AmbiguitySet
/-
Unique root of the robust-bidding equalizer, with both exact monotonicity claims.
Original mathematics: Bernhard Kasberger and Karl H. Schlag. Platform formulation:
mikedeng1; prior statement confirmation: Shuze Chen (not proof review).
The cited September3,2022 source was unavailable; the matching equation was checked
in the author-hosted March27,2023 version. The proof below is checked independently.
Retains the calculus body from this session's analytic-maximizer proof.
Alexander Richard Towell: research direction and archive stewardship.
OpenAI Codex: substantial formal proof construction, verification and documentation.
Lean/Mathlib contributors: calculus, intermediate values and proof infrastructure.
No mathematical novelty or independent human proof-review claim.
-/
import Mathlib
import Definitions.Def_RobustFPA_VarBid_ClosedForms

namespace ComparisonSource

namespace PriorEqualizer

open Set
open RobustFPA.VarBid
set_option autoImplicit false

namespace RobustBidResearch

lemma base_pos (τ L v b : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hLv : L < v) (hb : L ≤ b) : 0 < 1-τ+τ*((b-L)/(v-L)) := by
  have hp := mul_nonneg hτ0.le (div_nonneg (sub_nonneg.mpr hb) (sub_pos.mpr hLv).le)
  linarith

lemma plus_cont (n : ℕ) (τ L v : ℝ) : Continuous (uPlus n τ L v) := by
  unfold uPlus
  fun_prop

lemma plus_deriv (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hLv : L < v) :
    HasDerivAt (uPlus n τ L v)
      ((1-τ+τ*((b-L)/(v-L)))^(n-2) * ((n:ℝ)*τ/(v-L)) * (bTilde n τ L v-b)) b := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+2 := ⟨n-2,by omega⟩
  have hnum : (k:ℝ)+2 ≠ 0 := by positivity
  have hd : v-L ≠ 0 := ne_of_gt (sub_pos.mpr hLv)
  have ht : τ ≠ 0 := ne_of_gt hτ0
  have ha : HasDerivAt (fun z : ℝ => 1-τ+τ*((z-L)/(v-L))) (τ/(v-L)) b := by
    convert (hasDerivAt_const b (1-τ)).add ((((hasDerivAt_id b).sub_const L).div_const (v-L)).const_mul τ) using 1 <;> first | rfl | ring
  have h := ((hasDerivAt_const b v).sub (hasDerivAt_id b)).mul (ha.pow (k+1))
  unfold uPlus bTilde
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  convert h using 1 <;> try rfl
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply,Pi.sub_apply,id_eq,pow_succ]
  field_simp [hd,ht,hnum]
  <;> ring

lemma plus_maximum (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    IsMaxOn (uPlus n τ L v) (Ici L) (max (bTilde n τ L v) L) := by
  have hc := plus_cont n τ L v
  have hp : 0 ≤ (n:ℝ)*τ/(v-L) := div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le
  apply isMaxOn_Ici_of_deriv hc.continuousAt hc.continuousAt
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    have hbt : b < bTilde n τ L v := by
      rcases lt_max_iff.mp hb.2 with h | h
      · exact h
      · linarith [hb.1]
    exact mul_nonneg (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hb.1.le).le _) hp)
      (sub_nonneg.mpr hbt.le)
  · intro b hb
    have hbt : bTilde n τ L v ≤ b := (le_max_left _ _).trans hb.le
    have hLb : L ≤ b := (le_max_right _ _).trans hb.le
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hLb).le _) hp)
      (sub_nonpos.mpr hbt)

lemma peak_bounds (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hLv : L < v) : L ≤ peakBid n τ L v ∧ peakBid n τ L v < v := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have htilde : bTilde n τ L v < v := by
    unfold bTilde
    exact sub_lt_self _ (div_pos (sub_pos.mpr hLv) (mul_pos hn0 hτ0))
  exact ⟨le_max_left _ _,max_lt hLv htilde⟩
lemma gap_cont (n : ℕ) (τ L v : ℝ) : Continuous (fun b => uPlus n τ L v b-uMinus n τ L v b) := by
  unfold uPlus uMinus
  fun_prop
lemma gap_deriv (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ) (hLv : L < v) :
    HasDerivAt (fun z => uPlus n τ L v z-uMinus n τ L v z)
      (((1-τ+τ*((b-L)/(v-L)))^(n-2)-(τ*((b-L)/(v-L)))^(n-2)) *
      ((n:ℝ)*τ*(v-b)/(v-L)-1)-(1-τ)*(τ*((b-L)/(v-L)))^(n-2)) b := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+2 := ⟨n-2,by omega⟩
  have ha : HasDerivAt (fun z : ℝ => 1-τ+τ*((z-L)/(v-L))) (τ/(v-L)) b := by
    convert (hasDerivAt_const b (1-τ)).add ((((hasDerivAt_id b).sub_const L).div_const (v-L)).const_mul τ) using 1 <;> first | rfl | ring
  have hd : HasDerivAt (fun z : ℝ => τ*((z-L)/(v-L))) (τ/(v-L)) b := by
    convert (((hasDerivAt_id b).sub_const L).div_const (v-L)).const_mul τ using 1 <;> first | rfl | ring
  have hv := (hasDerivAt_const b v).sub (hasDerivAt_id b)
  have hh := (hv.mul (ha.pow (k+1))).sub ((hd.pow (k+1)).mul hv)
  unfold uPlus uMinus
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  convert hh using 1 <;> try rfl
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply,Pi.sub_apply,id_eq,pow_succ]
  field_simp [ne_of_gt (sub_pos.mpr hLv)]
  <;> ring
lemma plus_anti (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    AntitoneOn (uPlus n τ L v) (Icc (peakBid n τ L v) v) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (plus_cont n τ L v).continuousOn
  · intro b hb;exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Icc] at hb
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    have hLb : L ≤ b := (le_max_left L (bTilde n τ L v)).trans hb.1.le
    have htb : bTilde n τ L v ≤ b := (le_max_right L _).trans hb.1.le
    apply mul_nonpos_of_nonneg_of_nonpos _ (sub_nonpos.mpr htb)
    exact mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hLb).le _)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le)
lemma gap_strict (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    StrictAntiOn (fun b => uPlus n τ L v b-uMinus n τ L v b) (Icc (peakBid n τ L v) v) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (gap_cont n τ L v).continuousOn
  intro b hb
  rw [interior_Icc] at hb
  rw [(gap_deriv n hn τ L v b hLv).deriv]
  have hLb : L < b := (le_max_left L (bTilde n τ L v)).trans_lt hb.1
  have htb : bTilde n τ L v ≤ b := (le_max_right L _).trans hb.1.le
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hp : 0 < τ*((b-L)/(v-L)) := mul_pos hτ0 (div_pos (sub_pos.mpr hLb) (sub_pos.mpr hLv))
  have hab : τ*((b-L)/(v-L)) ≤ 1-τ+τ*((b-L)/(v-L)) := by linarith
  have hpow := pow_le_pow_left₀ hp.le hab (n-2)
  have hR : (n:ℝ)*τ*(v-b)/(v-L) ≤ 1 := by
    have hh : v-b ≤ (v-L)/((n:ℝ)*τ) := by dsimp [bTilde] at htb;linarith
    have hh' := (le_div_iff₀ (mul_pos hn0 hτ0)).mp hh
    apply (div_le_iff₀ (sub_pos.mpr hLv)).2
    nlinarith only [hh']
  have hfirst := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpow) (sub_nonpos.mpr hR)
  have hlast := mul_pos (sub_pos.mpr hτ1) (pow_pos hp (n-2))
  linarith only [hfirst,hlast]
end RobustBidResearch
#print axioms RobustBidResearch.gap_strict
theorem accepted_unique (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    MonotoneOn (fun b => uPlus n τ L v (peakBid n τ L v)-uPlus n τ L v b)
      (Icc (peakBid n τ L v) v) ∧
    StrictAntiOn (fun b => uPlus n τ L v b-uMinus n τ L v b) (Icc (peakBid n τ L v) v) ∧
    ∃! b : ℝ, peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b := by
  have hb := RobustBidResearch.peak_bounds n hn τ L v hτ0 hLv
  have ha := RobustBidResearch.plus_anti n hn τ L v hτ0 hτ1 hLv
  have hs := RobustBidResearch.gap_strict n hn τ L v hτ0 hτ1 hLv
  have hm : MonotoneOn (fun b => uPlus n τ L v (peakBid n τ L v)-uPlus n τ L v b)
      (Icc (peakBid n τ L v) v) := by
    intro a ha' b hb' hab
    exact sub_le_sub_left (ha ha' hb' hab) _
  refine ⟨hm,hs,?_⟩
  let F : ℝ → ℝ := fun b => uPlus n τ L v (peakBid n τ L v)-uPlus n τ L v b-
    (uPlus n τ L v b-uMinus n τ L v b)
  have hfc : Continuous F := by
    dsimp [F]
    exact (continuous_const.sub (RobustBidResearch.plus_cont n τ L v)).sub (RobustBidResearch.gap_cont n τ L v)
  have hlow : F (peakBid n τ L v) ≤ 0 := by
    have hd : 0 ≤ τ*((peakBid n τ L v-L)/(v-L)) :=
      mul_nonneg hτ0.le (div_nonneg (sub_nonneg.mpr hb.1) (sub_pos.mpr hLv).le)
    have hp := pow_le_pow_left₀ hd (by linarith :
      τ*((peakBid n τ L v-L)/(v-L)) ≤ 1-τ+τ*((peakBid n τ L v-L)/(v-L))) (n-1)
    have hh := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hb.2.le)
    dsimp [F,uPlus,uMinus]
    nlinarith only [hh]
  have hhigh : 0 ≤ F v := by
    have hp := RobustBidResearch.base_pos τ L v (peakBid n τ L v) hτ0 hτ1 hLv hb.1
    dsimp [F,uPlus,uMinus]
    simp only [sub_self,zero_mul,mul_zero,sub_zero]
    exact mul_nonneg (sub_nonneg.mpr hb.2.le) (pow_nonneg hp.le _)
  obtain ⟨b,hbi,hbF⟩ := intermediate_value_Icc hb.2.le hfc.continuousOn ⟨hlow,hhigh⟩
  have heq : Equation3 n τ L v b := by
    dsimp [F] at hbF
    exact sub_eq_zero.mp hbF
  refine ⟨b,⟨hbi.1,hbi.2,heq⟩,?_⟩
  intro z hz
  have hzi : z ∈ Icc (peakBid n τ L v) v := ⟨hz.1,hz.2.1⟩
  have hzE := hz.2.2
  unfold Equation3 at heq hzE
  rcases lt_trichotomy z b with h | h | h
  · have h1 := hm hzi hbi h.le
    have h2 := hs hzi hbi h
    linarith
  · exact h
  · have h1 := hm hbi hzi h.le
    have h2 := hs hbi hzi h
    linarith
#print axioms accepted_unique

namespace RobustBidResearch
lemma plus_max (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (b : ℝ) (hb : L ≤ b) :
    uPlus n τ L v b ≤ uPlus n τ L v (peakBid n τ L v) := by
  have h := plus_maximum n hn τ L v hτ0 hτ1 hLv hb
  simpa [peakBid,max_comm] using h
lemma plus_mono_before (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    MonotoneOn (uPlus n τ L v) (Icc L (peakBid n τ L v)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (plus_cont n τ L v).continuousOn
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Icc] at hb
    have hbt : b < bTilde n τ L v := by
      rcases lt_max_iff.mp hb.2 with h | h
      · linarith [hb.1]
      · exact h
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    exact mul_nonneg (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hb.1.le).le _)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le))
      (sub_nonneg.mpr hbt.le)
lemma plus_anti_after (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    AntitoneOn (uPlus n τ L v) (Ici (peakBid n τ L v)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (plus_cont n τ L v).continuousOn
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Ici] at hb
    have hLb : L ≤ b := (le_max_left _ _).trans hb.le
    have htb : bTilde n τ L v ≤ b := (le_max_right _ _).trans hb.le
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hLb).le _)
        (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le))
      (sub_nonpos.mpr htb)
lemma right_sup_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (hb : L ≤ b) :
    uPlus n τ L v b ≤ sSup (uPlus n τ L v '' Ioi b) := by
  have hbd : BddAbove (uPlus n τ L v '' Ioi b) := by
    refine ⟨uPlus n τ L v (peakBid n τ L v),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact plus_max n hn τ L v hτ0 hτ1 hLv x (hb.trans hx.le)
  exact ContinuousWithinAt.closure_le (by simp) (plus_cont n τ L v).continuousAt.continuousWithinAt
    continuousWithinAt_const (fun x hx => le_csSup hbd ⟨x,hx,rfl⟩)
lemma formulas_after (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (hb : peakBid n τ L v ≤ b) :
    tooHigh n τ L v b = uPlus n τ L v (peakBid n τ L v)-uPlus n τ L v b ∧
    tooLow n τ L v b = uPlus n τ L v b-uMinus n τ L v b := by
  have hLb : L ≤ b := (le_max_left _ _).trans hb
  have hmax := plus_max n hn τ L v hτ0 hτ1 hLv
  have hs1 : sSup (uPlus n τ L v '' Icc L b) = uPlus n τ L v (peakBid n τ L v) := by
    apply le_antisymm
    · apply csSup_le (s := uPlus n τ L v '' Icc L b) ⟨uPlus n τ L v L, L, ⟨le_rfl,hLb⟩,rfl⟩
      rintro _ ⟨x,hx,rfl⟩
      exact hmax x hx.1
    · apply le_csSup (s := uPlus n τ L v '' Icc L b) ⟨uPlus n τ L v (peakBid n τ L v),?_⟩ ⟨peakBid n τ L v,⟨le_max_left _ _,hb⟩,rfl⟩
      rintro _ ⟨x,hx,rfl⟩
      exact hmax x hx.1
  have hs2 : sSup (uPlus n τ L v '' Ioi b) = uPlus n τ L v b := by
    apply le_antisymm
    · apply csSup_le (s := uPlus n τ L v '' Ioi b) ⟨uPlus n τ L v (b+1),b+1,by simp,rfl⟩
      rintro _ ⟨x,hx,rfl⟩
      exact plus_anti_after n hn τ L v hτ0 hτ1 hLv hb (hb.trans hx.le) hx.le
    · exact right_sup_bound n hn τ L v b hτ0 hτ1 hLv hLb
  exact ⟨by rw [tooHigh,hs1],by rw [tooLow,hs2]⟩
lemma gap_pos (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (hLb : L ≤ b) (hbv : b < v) :
    uMinus n τ L v b < uPlus n τ L v b := by
  have hp : 0 ≤ τ*((b-L)/(v-L)) := mul_nonneg hτ0.le
    (div_nonneg (sub_nonneg.mpr hLb) (sub_pos.mpr hLv).le)
  have hpow := pow_lt_pow_left₀ (by linarith : τ*((b-L)/(v-L)) < 1-τ+τ*((b-L)/(v-L))) hp
    (by omega : n-1 ≠ 0)
  have h := mul_lt_mul_of_pos_left hpow (sub_pos.mpr hbv)
  simpa [uMinus,uPlus,mul_comm] using h
end RobustBidResearch

theorem solution (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    equalizerSet n τ L v = {b | peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b} := by
  ext b
  constructor
  · rintro ⟨⟨hLb,hbv⟩,heq⟩
    have hpb : peakBid n τ L v ≤ b := by
      by_contra h
      have hbp := lt_of_not_ge h
      have hhigh : tooHigh n τ L v b = 0 := by
        have hm := RobustBidResearch.plus_mono_before n hn τ L v hτ0 hτ1 hLv
        have hs : sSup (uPlus n τ L v '' Icc L b) = uPlus n τ L v b := by
          apply le_antisymm
          · apply csSup_le (s := uPlus n τ L v '' Icc L b) ⟨uPlus n τ L v b,b,⟨hLb,le_rfl⟩,rfl⟩
            rintro _ ⟨x,hx,rfl⟩
            exact hm ⟨hx.1,hx.2.trans hbp.le⟩ ⟨hLb,hbp.le⟩ hx.2
          · apply le_csSup (s := uPlus n τ L v '' Icc L b) ⟨uPlus n τ L v b,?_⟩ ⟨b,⟨hLb,le_rfl⟩,rfl⟩
            rintro _ ⟨x,hx,rfl⟩
            exact hm ⟨hx.1,hx.2.trans hbp.le⟩ ⟨hLb,hbp.le⟩ hx.2
        rw [tooHigh,hs,sub_self]
      have hbound := RobustBidResearch.right_sup_bound n hn τ L v b hτ0 hτ1 hLv hLb
      have hpos := RobustBidResearch.gap_pos n hn τ L v b hτ0 hτ1 hLv hLb
        (hbp.trans (RobustBidResearch.peak_bounds n hn τ L v hτ0 hLv).2)
      rw [hhigh] at heq
      unfold tooLow at heq
      linarith
    have hh := RobustBidResearch.formulas_after n hn τ L v b hτ0 hτ1 hLv hpb
    exact ⟨hpb,hbv,by dsimp [Equation3];rw [hh.1,hh.2] at heq;exact heq⟩
  · rintro ⟨hpb,hbv,heq⟩
    have hh := RobustBidResearch.formulas_after n hn τ L v b hτ0 hτ1 hLv hpb
    exact ⟨⟨(le_max_left _ _).trans hpb,hbv⟩,by rw [hh.1,hh.2];exact heq⟩
#print axioms solution

end PriorEqualizer

/- Strict bidder-count comparison. Reuses the complete accepted equalizer proof
above (submission a451dfdb-e5d9-46c6-a666-5518064e9596; SHA256
2f476e38fe4faadea4a8ebea46b5eeda569961c7036528d5d57dfcd87b5d8e97),
including its attribution. New argument compares consecutive exponents against
the old maximum and the strict positive correction (1-tau)*uMinus.
Alexander Richard Towell directed the work; OpenAI Codex constructed and checked
this formal proof. No mathematical novelty or independent human review claimed. -/
open Set RobustFPA.VarBid PriorEqualizer.RobustBidResearch

namespace BidCountComparison

noncomputable def base (τ L v b : ℝ) : ℝ := 1-τ+τ*((b-L)/(v-L))

lemma plus_step (n : ℕ) (hn : 1 ≤ n) (τ L v b : ℝ) :
    uPlus (n+1) τ L v b = base τ L v b * uPlus n τ L v b := by
  unfold uPlus base
  rw [show n+1-1 = (n-1)+1 by omega, pow_succ]
  ring

lemma minus_step (n : ℕ) (hn : 1 ≤ n) (τ L v b : ℝ) :
    uMinus (n+1) τ L v b = (τ*((b-L)/(v-L))) * uMinus n τ L v b := by
  unfold uMinus
  rw [show n+1-1 = (n-1)+1 by omega, pow_succ]
  ring

lemma root_interior (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v)
    (hb : peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b) :
    L < b ∧ b < v := by
  have hp := peak_bounds n hn τ L v hτ0 hLv
  have hmaxpos : 0 < uPlus n τ L v (peakBid n τ L v) := by
    exact mul_pos (sub_pos.mpr hp.2) (pow_pos (base_pos τ L v _ hτ0 hτ1 hLv hp.1) _)
  have hbv : b < v := by
    by_contra h
    have he : b=v := le_antisymm hb.2.1 (le_of_not_gt h)
    have hEq := hb.2.2
    simp [Equation3, he, uPlus, uMinus] at hEq
    have : uPlus n τ L v (peakBid n τ L v) = 0 := by
      simpa [uPlus] using hEq
    linarith
  have hpb : peakBid n τ L v < b := by
    by_contra h
    have he : b=peakBid n τ L v := le_antisymm (le_of_not_gt h) hb.1
    have hgap := gap_pos n hn τ L v (peakBid n τ L v) hτ0 hτ1 hLv hp.1 hp.2
    have hEq := hb.2.2
    rw [he] at hEq
    unfold Equation3 at hEq
    linarith
  exact ⟨hp.1.trans_lt hpb,hbv⟩

lemma root_increasing (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (b b' : ℝ)
    (hb : peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b)
    (hb' : peakBid (n+1) τ L v ≤ b' ∧ b' ≤ v ∧ Equation3 (n+1) τ L v b') :
    b < b' := by
  have hn1 : 1 ≤ n := by omega
  have hn' : 2 ≤ n+1 := by omega
  have hp := peak_bounds n hn τ L v hτ0 hLv
  have hp' := peak_bounds (n+1) hn' τ L v hτ0 hLv
  have hbi := root_interior n hn τ L v b hτ0 hτ1 hLv hb
  by_cases hbp : b < peakBid (n+1) τ L v
  · exact hbp.trans_le hb'.1
  have hpb : peakBid (n+1) τ L v ≤ b := le_of_not_gt hbp
  have hbase : base τ L v (peakBid (n+1) τ L v) ≤ base τ L v b := by
    unfold base
    gcongr
  have hmaxnonneg : 0 ≤ uPlus n τ L v (peakBid n τ L v) := by
    exact mul_nonneg (sub_nonneg.mpr hp.2.le)
      (pow_nonneg (base_pos τ L v _ hτ0 hτ1 hLv hp.1).le _)
  have hpeak : uPlus (n+1) τ L v (peakBid (n+1) τ L v) ≤
      base τ L v b * uPlus n τ L v (peakBid n τ L v) := by
    rw [plus_step n hn1]
    calc
      _ ≤ base τ L v (peakBid (n+1) τ L v) *
          uPlus n τ L v (peakBid n τ L v) :=
        mul_le_mul_of_nonneg_left
          (plus_max n hn τ L v hτ0 hτ1 hLv _ hp'.1)
          (base_pos τ L v _ hτ0 hτ1 hLv hp'.1).le
      _ ≤ _ := mul_le_mul_of_nonneg_right hbase hmaxnonneg
  have hminuspos : 0 < uMinus n τ L v b := by
    exact mul_pos (pow_pos (mul_pos hτ0 (div_pos (sub_pos.mpr hbi.1)
      (sub_pos.mpr hLv))) _) (sub_pos.mpr hbi.2)
  have hstrict : uPlus (n+1) τ L v (peakBid (n+1) τ L v) <
      2*uPlus (n+1) τ L v b-uMinus (n+1) τ L v b := by
    have hEq := hb.2.2
    unfold Equation3 at hEq
    have hpositive := mul_pos (sub_pos.mpr hτ1) hminuspos
    have hEqual : uPlus n τ L v (peakBid n τ L v) =
        2*uPlus n τ L v b-uMinus n τ L v b := by linarith only [hEq]
    rw [hEqual] at hpeak
    rw [plus_step n hn1 τ L v b, minus_step n hn1 τ L v b]
    dsimp [base] at hpeak ⊢
    nlinarith only [hpeak, hpositive]
  by_contra h
  have hbb : b' ≤ b := le_of_not_gt h
  have hplus := plus_anti (n+1) hn' τ L v hτ0 hτ1 hLv
    ⟨hb'.1,hb'.2.1⟩ ⟨hpb,hb.2.1⟩ hbb
  have hgap := (gap_strict (n+1) hn' τ L v hτ0 hτ1 hLv).antitoneOn
    ⟨hb'.1,hb'.2.1⟩ ⟨hpb,hb.2.1⟩ hbb
  have hEq' := hb'.2.2
  unfold Equation3 at hEq'
  linarith

end BidCountComparison

theorem solution (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (b b' : ℝ)
    (hb : peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b)
    (hb' : peakBid (n+1) τ L v ≤ b' ∧ b' ≤ v ∧ Equation3 (n+1) τ L v b') :
    b < b' := BidCountComparison.root_increasing n hn τ L v hτ0 hτ1 hLv b b' hb hb'

#print axioms solution

end ComparisonSource

namespace AcceptedMinimax
/-
Robust first-price minimax characterization, 23 October 2026.
Original auction mathematics: Bernhard Kasberger and Karl H. Schlag. The
platform cites the 3 September 2022 version; the inspected author PDF is dated
27 March 2023. This proof concerns the exact corrected uniform-G platform model.
Reuses actual accepted proof bodies for maximal loss (submission
74bdadfc-ba79-4d20-9ef0-26dafed851cf; SHA256
341e0e25ba68668fad1301fbae1c5be43f5d473d39702ca00696eae66293f4a4)
and equalizer-set/unique-root analysis (target
05be7290-715f-4ed8-a1f0-c6149f96bff9; SHA256
2f476e38fe4faadea4a8ebea46b5eeda569961c7036528d5d57dfcd87b5d8e97).
Their helpers and inherited credits are retained; earlier work is not counted
again. New work proves strict global minimization, including bids below the
support and above value, the full minimax characterization and loss at the
minimizer. Strict bidder-count monotonicity is not proved here.
Alexander Richard Towell directed the research; OpenAI Codex substantially
constructed, checked and documented this argument. mikedeng1 supplied the
corrected model; Shuze Chen confirmed its statement, not this proof. Lean and
Mathlib supply foundations. No novelty or independent human review claimed.
-/
open Set MeasureTheory RobustFPA.VarBid
set_option autoImplicit false

open scoped ENNReal

namespace RobustFPA.VarBid

lemma uniform_probability (L v : ℝ) (hLv : L < v) : IsProbabilityMeasure (uniformG L v) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hLv))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

lemma uniform_lower_support (L v : ℝ) : uniformG L v (Set.Iio L) = 0 := by
  have h : Set.Icc L v ∩ Set.Iio L = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_lt_of_ge hx.1.1) hx.2
  unfold uniformG
  rw [ProbabilityTheory.cond_apply' measurableSet_Iio, h]
  simp

lemma common_admissible (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (x : ℝ) (hx : L ≤ x) :
    commonBidEnv n τ (uniformG L v) x ∈ varBidSet n τ L (uniformG L v) := by
  refine ⟨hn, hL, hτ0.le, hτ1.le, uniform_probability L v hLv,
    uniform_lower_support L v, Measure.dirac (fun _ => x), inferInstance, ?_, rfl⟩
  simp [Measure.dirac_apply', hx]

lemma bern_probability (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    IsProbabilityMeasure (bern τ) := by
  constructor
  simp only [bern, Measure.add_apply, MeasurableSet.univ, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  simp only [ENNReal.smul_one]
  rw [← ENNReal.coe_add, ← Real.toNNReal_add hτ0]
  · simp
  · linarith

lemma measurable_mix {m : ℕ} :
    Measurable (fun p : (Fin m → Bool × ℝ) × (Fin m → ℝ) => mixBids p.1 p.2) := by
  apply measurable_pi_lambda
  intro j
  unfold mixBids
  exact Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

lemma common_law (n : ℕ) (τ : ℝ) (G : Measure ℝ) [IsFiniteMeasure G] (x : ℝ) :
    commonBidEnv n τ G x =
      (constrainedLaw (n-1) τ G).map (fun cy j => if (cy j).1 then (cy j).2 else x) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  letI : IsFiniteMeasure (constrainedLaw (n-1) τ G) := by unfold constrainedLaw; infer_instance
  unfold commonBidEnv envOf
  rw [Measure.prod_dirac, Measure.map_map measurable_mix (by fun_prop)]
  rfl

lemma component_law (τ x : ℝ) (G : Measure ℝ) [IsProbabilityMeasure G] :
    ((bern τ).prod G).map (fun p : Bool × ℝ => if p.1 then p.2 else x) =
      Real.toNNReal τ • G + Real.toNNReal (1-τ) • Measure.dirac x := by
  have hm : Measurable (fun p : Bool × ℝ => if p.1 then p.2 else x) := by
    exact Measurable.ite (by measurability) measurable_snd measurable_const
  unfold bern
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul,
    Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map hm measurable_prodMk_left, Measure.map_map hm measurable_prodMk_left]
  simp [Function.comp_def]

lemma common_product (n : ℕ) (τ : ℝ) (G : Measure ℝ) [IsProbabilityMeasure G] (x : ℝ) :
    commonBidEnv n τ G x = Measure.pi (fun _ : Fin (n-1) =>
      Real.toNNReal τ • G + Real.toNNReal (1-τ) • Measure.dirac x) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  rw [common_law]
  unfold constrainedLaw
  have hm : Measurable (fun p : Bool × ℝ => if p.1 then p.2 else x) := by
    exact Measurable.ite (by measurability) measurable_snd measurable_const
  rw [Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  simp_rw [component_law]

lemma uniform_noatoms (L v : ℝ) : NullSingletonClass (uniformG L v) := by
  constructor
  intro x
  unfold uniformG
  rw [ProbabilityTheory.cond_apply' (measurableSet_singleton x)]
  have h : (volume : Measure ℝ) (Set.Icc L v ∩ {x}) = 0 :=
    measure_mono_null Set.inter_subset_right (measure_singleton x)
  simp [h]

lemma uniform_Iio (L v b : ℝ) (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) :
    uniformG L v (Set.Iio b) = ENNReal.ofReal ((b-L)/(v-L)) := by
  have hi : Set.Icc L v ∩ Set.Iio b = Set.Ico L b := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.le.trans hbv⟩, h.2⟩
  unfold uniformG
  rw [ProbabilityTheory.cond_apply' measurableSet_Iio, hi, Real.volume_Icc, Real.volume_Ico]
  rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hLv)]
  rw [div_eq_mul_inv, mul_comm]

lemma product_payoff (m : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v b : ℝ) (hμ : μ {b} = 0) :
    expUtil v b (Measure.pi (fun _ : Fin m => μ)) =
      (μ (Set.Iio b)).toReal ^ m * (v-b) := by
  classical
  let S : Set (Fin m → ℝ) := Set.univ.pi (fun _ => Set.Iio b)
  have hs : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Iio)
  have hn : ∀ᵐ o ∂Measure.pi (fun _ : Fin m => μ), ∀ j, o j ≠ b := by
    rw [ae_all_iff]
    intro j
    apply ae_iff.mpr
    simpa only [not_not, Set.preimage, Set.mem_singleton_iff, Function.eval] using
      (Measure.pi_eval_preimage_null (fun _ : Fin m => μ) (i := j) hμ)
  have he : (fun o => payoff v b o) =ᵐ[Measure.pi (fun _ : Fin m => μ)]
      S.indicator (fun _ => v-b) := by
    filter_upwards [hn] with o ho
    by_cases hw : ∀ j, o j ≤ b
    · have hm : o ∈ S := by
        simpa [S, Set.mem_pi] using (fun j => lt_of_le_of_ne (hw j) (ho j))
      have hf : (Finset.univ.filter (fun j => o j = b)) = ∅ := by
        ext j
        simp [ho j]
      simp [payoff, hw, hf, Set.indicator_of_mem hm]
    · have hm : o ∉ S := by
        intro h
        have hh : ∀ j, o j < b := by simpa [S, Set.mem_pi] using h
        exact hw (fun j => (hh j).le)
      simp [payoff, hw, Set.indicator_of_notMem hm]
  unfold expUtil
  rw [integral_congr_ae he, integral_indicator_const _ hs]
  simp only [Measure.real, S, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow, smul_eq_mul]

lemma common_no_tie (τ L v b x : ℝ) (hxb : x ≠ b) :
    (Real.toNNReal τ • uniformG L v + Real.toNNReal (1-τ) • Measure.dirac x) {b} = 0 := by
  letI := uniform_noatoms L v
  simp [hxb]

lemma common_utility (n : ℕ) (τ L v b x : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) (hxb : x ≠ b) :
    expUtil v b (commonBidEnv n τ (uniformG L v) x) =
      (τ * ((b-L)/(v-L)) + if x < b then 1-τ else 0) ^ (n-1) * (v-b) := by
  letI := uniform_probability L v hLv
  rw [common_product, product_payoff _ _ _ _ (common_no_tie τ L v b x hxb)]
  congr 2
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, uniform_Iio L v b hLv hLb hbv]
  have hratio : 0 ≤ (b-L)/(v-L) := div_nonneg (sub_nonneg.mpr hLb) (sub_pos.mpr hLv).le
  simp [ENNReal.toReal_ofReal hratio, Real.toNNReal_of_nonneg hτ0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hτ1), Measure.dirac_apply']
  by_cases hx : x < b <;> simp [Set.indicator, hx]

lemma common_utility_above (n : ℕ) (τ L v b x : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) (hxb : x < b) :
    expUtil v b (commonBidEnv n τ (uniformG L v) x) = uPlus n τ L v b := by
  rw [common_utility n τ L v b x hτ0 hτ1 hLv hLb hbv hxb.ne]
  simp only [if_pos hxb, uPlus]
  ring

lemma common_utility_below (n : ℕ) (τ L v b x : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) (hbx : b < x) :
    expUtil v b (commonBidEnv n τ (uniformG L v) x) = uMinus n τ L v b := by
  rw [common_utility n τ L v b x hτ0 hτ1 hLv hLb hbv hbx.ne']
  simp [not_lt_of_ge hbx.le, uMinus]

lemma payoff_measurable (m : ℕ) (v b : ℝ) : Measurable (payoff (m := m) v b) := by
  classical
  have hc : Measurable (fun o : Fin m → ℝ =>
      ((Finset.univ.filter (fun j => o j = b)).card : ℝ)) := by
    have hh : Measurable (fun o : Fin m → ℝ =>
        ∑ j : Fin m, if o j = b then (1:ℝ) else 0) := by
      apply Finset.measurable_sum
      intro j _
      exact Measurable.ite (by measurability) measurable_const measurable_const
    simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hh
  unfold payoff
  exact Measurable.ite (by measurability) (measurable_const.div (hc.add_const 1)) measurable_const

lemma payoff_bound (m : ℕ) (v b : ℝ) (o : Fin m → ℝ) :
    ‖payoff v b o‖ ≤ |v-b| := by
  classical
  unfold payoff
  split_ifs
  · have hd : (1:ℝ) ≤ ((Finset.univ.filter (fun j => o j = b)).card : ℝ) + 1 := by have h := Nat.cast_nonneg (α := ℝ) (Finset.univ.filter (fun j => o j = b)).card; linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hd)]
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr (by nlinarith [abs_nonneg (v-b)])
  · simp

lemma payoff_integrable (m : ℕ) (v b : ℝ) (B : Measure (Fin m → ℝ)) [IsFiniteMeasure B] :
    Integrable (payoff v b) B := by
  apply Integrable.mono' (integrable_const |v-b|) (payoff_measurable m v b).aestronglyMeasurable
  exact Filter.Eventually.of_forall (payoff_bound m v b)

lemma environment_probability (n : ℕ) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (H : Measure (Fin (n-1) → ℝ)) [IsProbabilityMeasure H] :
    IsProbabilityMeasure (envOf n τ G H) := by
  letI := bern_probability τ hτ0 hτ1
  letI : IsProbabilityMeasure (constrainedLaw (n-1) τ G) := by
    unfold constrainedLaw
    infer_instance
  exact Measure.isProbabilityMeasure_map measurable_mix.aemeasurable

lemma admissible_probability (n : ℕ) (τ L : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L G) :
    IsProbabilityMeasure B := by
  rcases hB with ⟨_, _, hτ0, hτ1, hG, _, H, hH, _, rfl⟩
  letI := hG
  letI := hH
  exact environment_probability n τ hτ0 hτ1 G H

lemma payoff_le_value (m : ℕ) (v b : ℝ) (hv : 0 ≤ v) (hb : 0 ≤ b) (o : Fin m → ℝ) :
    payoff v b o ≤ v := by
  classical
  unfold payoff
  split_ifs
  · have hc : 0 ≤ ((Finset.univ.filter (fun j => o j = b)).card : ℝ) := Nat.cast_nonneg _
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · exact hv

lemma expUtil_le_value (m : ℕ) (v b : ℝ) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (B : Measure (Fin m → ℝ)) [IsProbabilityMeasure B] : expUtil v b B ≤ v := by
  have h := integral_mono (payoff_integrable m v b B) (integrable_const v)
    (payoff_le_value m v b hv hb)
  simpa [expUtil] using h

lemma bestUtil_bounds (m : ℕ) (v : ℝ) (hv : 0 ≤ v)
    (B : Measure (Fin m → ℝ)) [IsProbabilityMeasure B] :
    0 ≤ bestUtil v B ∧ bestUtil v B ≤ v := by
  have hB : BddAbove ((fun b => expUtil v b B) '' Set.Ici 0) := by
    refine ⟨v, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact expUtil_le_value m v b hv hb B
  have hzero : expUtil v v B = 0 := by simp [expUtil, payoff]
  constructor
  · have hh : expUtil v v B ≤ bestUtil v B := le_csSup hB ⟨v, hv, rfl⟩
    simpa only [hzero] using hh
  · have hn : ((fun b : ℝ => expUtil v b B) '' Set.Ici 0).Nonempty :=
      ⟨expUtil v 0 B, 0, by simp, rfl⟩
    exact csSup_le hn (by rintro _ ⟨b, hb, rfl⟩; exact expUtil_le_value m v b hv hb B)

lemma expUtil_lower (m : ℕ) (v b : ℝ) (B : Measure (Fin m → ℝ)) [IsProbabilityMeasure B] :
    -|v-b| ≤ expUtil v b B := by
  have hp : ∀ o : Fin m → ℝ, -|v-b| ≤ payoff v b o := by
    intro o
    have h := payoff_bound m v b o
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).1
  have h := integral_mono (integrable_const (-|v-b|)) (payoff_integrable m v b B) hp
  simpa [expUtil] using h

lemma losses_bounded (n : ℕ) (τ L v b : ℝ) (hv : 0 ≤ v)
    (G : Measure ℝ) [IsFiniteMeasure G] :
    BddAbove ((fun B => loss v b B) '' varBidSet n τ L G) := by
  refine ⟨v+|v-b|, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  letI := admissible_probability n τ L G B hB
  have hu := (bestUtil_bounds (n-1) v hv B).2
  have hl := expUtil_lower (n-1) v b B
  unfold loss
  linarith

lemma common_gain_le_maxLoss (n : ℕ) (hn : 2 ≤ n) (τ L v b h x : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hh : 0 ≤ h) (hx : L ≤ x) :
    expUtil v h (commonBidEnv n τ (uniformG L v) x) -
      expUtil v b (commonBidEnv n τ (uniformG L v) x) ≤
      maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  have hB := common_admissible n hn τ L v hτ0 hτ1 hL hLv x hx
  let B := commonBidEnv n τ (uniformG L v) x
  letI : IsProbabilityMeasure B := admissible_probability n τ L (uniformG L v) B hB
  have hv : 0 ≤ v := hL.trans hLv.le
  have hu : BddAbove ((fun z => expUtil v z B) '' Set.Ici 0) := by
    refine ⟨v, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact expUtil_le_value (n-1) v z hv hz B
  have hb : expUtil v h B ≤ bestUtil v B := le_csSup hu ⟨h, hh, rfl⟩
  have hl : loss v b B ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) :=
    le_csSup (losses_bounded n τ L v b hv (uniformG L v)) ⟨B, hB, rfl⟩
  exact (sub_le_sub_right hb _).trans hl

lemma low_gain_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b h : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbh : b < h) (hhv : h ≤ v) :
    uPlus n τ L v h - uMinus n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  let x := (b+h)/2
  have hbx : b < x := by dsimp [x]; linarith
  have hxh : x < h := by dsimp [x]; linarith
  have q := common_gain_le_maxLoss n hn τ L v b h x hτ0 hτ1 hL hLv
    (hL.trans (hLb.trans hbh.le)) (hLb.trans hbx.le)
  rw [common_utility_above n τ L v h x hτ0.le hτ1.le hLv (hLb.trans hbh.le) hhv hxh,
    common_utility_below n τ L v b x hτ0.le hτ1.le hLv hLb (hbh.le.trans hhv) hbx] at q
  exact q

lemma high_gain_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b h : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLh : L < h) (hhb : h ≤ b) (hbv : b ≤ v) :
    uPlus n τ L v h - uPlus n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  let x := (L+h)/2
  have hLx : L < x := by dsimp [x]; linarith
  have hxh : x < h := by dsimp [x]; linarith
  have q := common_gain_le_maxLoss n hn τ L v b h x hτ0 hτ1 hL hLv
    (hL.trans hLh.le) hLx.le
  rw [common_utility_above n τ L v h x hτ0.le hτ1.le hLv hLh.le (hhb.trans hbv) hxh,
    common_utility_above n τ L v b x hτ0.le hτ1.le hLv (hLh.le.trans hhb) hbv (hxh.trans_le hhb)] at q
  exact q

lemma payoff_nonnegative {m : ℕ} (v b : ℝ) (hbv : b ≤ v) (o : Fin m → ℝ) :
    0 ≤ payoff v b o := by
  unfold payoff
  split_ifs <;> positivity

lemma mixed_payoff_lower {m : ℕ} (v b x : ℝ) (hbv : b ≤ v) (hbx : b < x)
    (cy : Fin m → Bool × ℝ) (z : Fin m → ℝ) :
    payoff v b (mixBids cy (fun _ => x)) ≤ payoff v b (mixBids cy z) := by
  classical
  by_cases hw : ∀ j, mixBids cy (fun _ => x) j ≤ b
  · have hall : ∀ j, (cy j).1 = true := by
      intro j
      have h := hw j
      unfold mixBids at h
      cases hc : (cy j).1
      · simp [hc] at h
        linarith
      · rfl
    have he : mixBids cy (fun _ => x) = mixBids cy z := by
      funext j
      simp [mixBids, hall j]
    rw [he]
  · rw [payoff, if_neg hw]
    exact payoff_nonnegative v b hbv _

lemma mixed_payoff_upper {m : ℕ} (v b x : ℝ) (hbv : b ≤ v) (hxb : x < b)
    (cy : Fin m → Bool × ℝ) (z : Fin m → ℝ) :
    payoff v b (mixBids cy z) ≤ payoff v b (mixBids cy (fun _ => x)) := by
  classical
  by_cases hw : ∀ j, mixBids cy z j ≤ b
  · have hw' : ∀ j, mixBids cy (fun _ => x) j ≤ b := by
      intro j
      have h := hw j
      unfold mixBids at h ⊢
      split_ifs with hc
      · simpa [hc] using h
      · exact hxb.le
    have hsub : (Finset.univ.filter (fun j => mixBids cy (fun _ => x) j = b)) ⊆
        (Finset.univ.filter (fun j => mixBids cy z j = b)) := by
      intro j hj
      have hh := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold mixBids at hh ⊢
      split_ifs with hc
      · simpa [hc] using hh
      · exact False.elim (hxb.ne (by simpa [hc] using hh))
    have hc := Finset.card_le_card hsub
    have hcr : ((Finset.univ.filter (fun j => mixBids cy (fun _ => x) j = b)).card : ℝ) ≤
      ((Finset.univ.filter (fun j => mixBids cy z j = b)).card : ℝ) := by exact_mod_cast hc
    simp only [payoff, if_pos hw, if_pos hw']
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hbv) (by positivity) (by linarith)
  · rw [payoff, if_neg hw]
    exact payoff_nonnegative v b hbv _

lemma mixed_integrable {m : ℕ} (v b : ℝ) (F : ((Fin m → Bool × ℝ) × (Fin m → ℝ)) → (Fin m → ℝ))
    (hF : Measurable F) (μ : Measure ((Fin m → Bool × ℝ) × (Fin m → ℝ))) [IsFiniteMeasure μ] :
    Integrable (fun p => payoff v b (F p)) μ := by
  apply Integrable.mono' (integrable_const |v-b|)
    ((payoff_measurable m v b).comp hF).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => payoff_bound m v b (F p))

lemma environment_integral (n : ℕ) (τ v b : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (H : Measure (Fin (n-1) → ℝ)) :
    expUtil v b (envOf n τ G H) =
      ∫ p, payoff v b (mixBids p.1 p.2) ∂((constrainedLaw (n-1) τ G).prod H) := by
  unfold expUtil envOf
  exact integral_map_of_stronglyMeasurable measurable_mix (payoff_measurable _ v b).stronglyMeasurable

set_option synthInstance.maxHeartbeats 200000 in
lemma common_integral (n : ℕ) (τ v b x : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (H : Measure (Fin (n-1) → ℝ)) [IsProbabilityMeasure H] :
    (∫ p, payoff v b (mixBids p.1 (fun _ => x)) ∂((constrainedLaw (n-1) τ G).prod H)) =
      expUtil v b (commonBidEnv n τ G x) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  letI : IsFiniteMeasure (constrainedLaw (n-1) τ G) := by unfold constrainedLaw; infer_instance
  rw [integral_fun_fst (μ := constrainedLaw (n-1) τ G) (ν := H)
    (fun cy => payoff v b (mixBids cy (fun _ => x)))]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [common_law]
  unfold expUtil
  symm
  apply integral_map_of_stronglyMeasurable
  · apply measurable_pi_lambda
    intro j
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  · exact (payoff_measurable _ v b).stronglyMeasurable

lemma environment_utility_bounds (n : ℕ) (τ L v b : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v)
    (H : Measure (Fin (n-1) → ℝ)) [IsProbabilityMeasure H] :
    uMinus n τ L v b ≤ expUtil v b (envOf n τ (uniformG L v) H) ∧
    expUtil v b (envOf n τ (uniformG L v) H) ≤ uPlus n τ L v b := by
  letI := bern_probability τ hτ0 hτ1
  letI := uniform_probability L v hLv
  letI : IsProbabilityMeasure (constrainedLaw (n-1) τ (uniformG L v)) := by
    unfold constrainedLaw
    infer_instance
  let μ := (constrainedLaw (n-1) τ (uniformG L v)).prod H
  have hi := mixed_integrable v b (fun p => mixBids p.1 p.2) measurable_mix μ
  have hix (x : ℝ) := mixed_integrable v b (fun p => mixBids p.1 (fun _ => x))
    (by apply measurable_pi_lambda; intro j; exact Measurable.ite (by measurability) (by fun_prop) measurable_const) μ
  rw [environment_integral]
  constructor
  · have hh := integral_mono (hix (b+1)) hi (fun p => mixed_payoff_lower v b (b+1) hbv (by linarith) p.1 p.2)
    change (∫ p, payoff v b (mixBids p.1 (fun _ => b+1)) ∂μ) ≤ _ at hh
    rw [common_integral, common_utility_below n τ L v b (b+1) hτ0 hτ1 hLv hLb hbv (by linarith)] at hh
    exact hh
  · have hh := integral_mono hi (hix (b-1)) (fun p => mixed_payoff_upper v b (b-1) hbv (by linarith) p.1 p.2)
    change _ ≤ (∫ p, payoff v b (mixBids p.1 (fun _ => b-1)) ∂μ) at hh
    rw [common_integral, common_utility_above n τ L v b (b-1) hτ0 hτ1 hLv hLb hbv (by linarith)] at hh
    exact hh

lemma admissible_utility_bounds (n : ℕ) (τ L v b : ℝ) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v)
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L (uniformG L v)) :
    uMinus n τ L v b ≤ expUtil v b B ∧ expUtil v b B ≤ uPlus n τ L v b := by
  rcases hB with ⟨_, _, hτ0, hτ1, _, _, H, hH, _, rfl⟩
  letI := hH
  exact environment_utility_bounds n τ L v b hτ0 hτ1 hLv hLb hbv H

lemma deviation_upper (n : ℕ) (τ L v b h : ℝ) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v) (hLh : L ≤ h) (hhv : h ≤ v)
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L (uniformG L v)) :
    expUtil v h B - expUtil v b B ≤ uPlus n τ L v h - uMinus n τ L v b := by
  exact sub_le_sub (admissible_utility_bounds n τ L v h hLv hLh hhv B hB).2
    (admissible_utility_bounds n τ L v b hLv hLb hbv B hB).1

lemma high_gain_closed (n : ℕ) (hn : 2 ≤ n) (τ L v b h : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLh : L ≤ h) (hhb : h ≤ b) (hbv : b ≤ v) :
    uPlus n τ L v h - uPlus n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  by_cases hLb : L < b
  · have hx : h ∈ closure (Set.Ioc L b) := by
      rw [closure_Ioc hLb.ne]
      exact ⟨hLh, hhb⟩
    have hc : Continuous (fun y => uPlus n τ L v y - uPlus n τ L v b) := by
      unfold uPlus
      fun_prop
    exact ContinuousWithinAt.closure_le hx hc.continuousWithinAt continuousWithinAt_const
      (fun y hy => high_gain_lower_bound n hn τ L v b y hτ0 hτ1 hL hLv hy.1 hy.2 hbv)
  · have he : h = b := by linarith
    have hlb : L ≤ b := hLh.trans hhb
    have hh := common_gain_le_maxLoss n hn τ L v b b L hτ0 hτ1 hL hLv (hL.trans hlb) le_rfl
    simpa [he] using hh

lemma tooHigh_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v) :
    tooHigh n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  unfold tooHigh
  apply sub_le_iff_le_add.mpr
  apply csSup_le
  · exact ⟨uPlus n τ L v L, L, ⟨le_rfl, hLb⟩, rfl⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact (sub_le_iff_le_add.mp (high_gain_closed n hn τ L v b h hτ0 hτ1 hL hLv hh.1 hh.2 hbv))

lemma maxLoss_nonnegative (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) (hb : 0 ≤ b) :
    0 ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  simpa using common_gain_le_maxLoss n hn τ L v b b L hτ0 hτ1 hL hLv hb le_rfl

lemma tooLow_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v) :
    tooLow n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  unfold tooLow
  apply sub_le_iff_le_add.mpr
  apply csSup_le
  · refine ⟨uPlus n τ L v (b+1), b+1, ?_, rfl⟩
    simp
  · rintro _ ⟨h, hh, rfl⟩
    apply sub_le_iff_le_add.mp
    by_cases hhv : h ≤ v
    · exact low_gain_lower_bound n hn τ L v b h hτ0 hτ1 hL hLv hLb hh hhv
    · have hp : uPlus n τ L v h ≤ 0 := by
        unfold uPlus
        apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
        have hhL : 0 ≤ h-L := by linarith [hh]
        have ht : 0 ≤ 1-τ := by linarith
        positivity
      have hm : 0 ≤ uMinus n τ L v b := by
        unfold uMinus
        have hbL : 0 ≤ b-L := sub_nonneg.mpr hLb
        have hvb : 0 ≤ v-b := sub_nonneg.mpr hbv
        positivity
      have hz := maxLoss_nonnegative n hn τ L v b hτ0 hτ1 hL hLv (hL.trans hLb)
      linarith

lemma analytic_max_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v) :
    max (tooHigh n τ L v b) (tooLow n τ L v b) ≤
      maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  exact max_le (tooHigh_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb hbv)
    (tooLow_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb hbv)

/-- Preserve the common-law dependence through coordinatewise CDF ratios. -/
lemma product_gain_bound {ι : Type*} [Fintype ι] (a c : ι → ℝ)
    (A C r s : ℝ) (hA : 0 ≤ A) (hC : 0 < C) (hr : 0 ≤ r)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (hcC : ∀ i, c i ≤ C) (hcross : ∀ i, a i * C ≤ A * c i) :
    r * (∏ i, a i) - s * (∏ i, c i) ≤
      max (r * A ^ Fintype.card ι - s * C ^ Fintype.card ι) 0 := by
  classical
  let t := A / C
  have ht : 0 ≤ t := div_nonneg hA hC.le
  have hratio : ∀ i, a i ≤ t * c i := by
    intro i
    change a i ≤ (A / C) * c i
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hC).mpr (hcross i)
  have hp : (∏ i, a i) ≤ t ^ Fintype.card ι * ∏ i, c i := by
    have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => ha i) (fun i _ => hratio i)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h
  have hc0 : 0 ≤ ∏ i, c i := Finset.prod_nonneg (fun i _ => hc i)
  have hpc : (∏ i, c i) ≤ C ^ Fintype.card ι := by
    have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => hc i) (fun i _ => hcC i)
    simpa only [Finset.prod_const, Finset.card_univ] using h
  have he : t ^ Fintype.card ι * C ^ Fintype.card ι = A ^ Fintype.card ι := by
    dsimp [t]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hC.ne')]
  have hgain : r * (∏ i, a i) - s * (∏ i, c i) ≤
      (r * t ^ Fintype.card ι - s) * ∏ i, c i := by
    nlinarith [mul_le_mul_of_nonneg_left hp hr]
  by_cases hsign : 0 ≤ r * t ^ Fintype.card ι - s
  · have h := mul_le_mul_of_nonneg_left hpc hsign
    have hh : (r * t ^ Fintype.card ι - s) * C ^ Fintype.card ι =
        r * A ^ Fintype.card ι - s * C ^ Fintype.card ι := by rw [sub_mul, mul_assoc, he]
    rw [hh] at h
    exact (hgain.trans h).trans (le_max_left _ _)
  · exact (hgain.trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign) hc0)).trans
      (le_max_right _ _)

/-- With heterogeneous unconstrained bids, each opponent has a low or high CDF factor. -/
lemma binary_product_gain_bound {ι : Type*} [Fintype ι] (low : ι → Bool)
    (τ p q r s : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hr : 0 ≤ r) :
    r * (∏ i, (τ * p + if low i then 1 - τ else 0)) -
      s * (∏ i, (τ * q + if low i then 1 - τ else 0)) ≤
      max (r * (1 - τ + τ * p) ^ Fintype.card ι -
        s * (1 - τ + τ * q) ^ Fintype.card ι) 0 := by
  have hq : 0 ≤ q := hp.trans hpq
  apply product_gain_bound _ _ (1 - τ + τ * p) (1 - τ + τ * q) r s
    (by positivity) (by positivity) hr
  · intro i
    cases low i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity
  · intro i
    cases low i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity
  · intro i
    cases low i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  · intro i
    cases low i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr hpq)]
    · nlinarith

noncomputable def favorableProjection {m : ℕ} (h b : ℝ) (z : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if z i ≤ h then h - 1 else b + 1

lemma projected_gain_upper {m : ℕ} (v h b : ℝ) (hhb : h < b) (hbv : b ≤ v)
    (cy : Fin m → Bool × ℝ) (z : Fin m → ℝ) :
    payoff v h (mixBids cy z) - payoff v b (mixBids cy z) ≤
      payoff v h (mixBids cy (favorableProjection h b z)) -
        payoff v b (mixBids cy (favorableProjection h b z)) := by
  classical
  have hup : payoff v h (mixBids cy z) ≤ payoff v h (mixBids cy (favorableProjection h b z)) := by
    by_cases hw : ∀ i, mixBids cy z i ≤ h
    · have hw' : ∀ i, mixBids cy (favorableProjection h b z) i ≤ h := by
        intro i
        have hi := hw i
        by_cases hc : (cy i).1 = true
        · simpa [mixBids, hc] using hi
        · have hz : z i ≤ h := by simpa [mixBids, hc] using hi
          simp [mixBids, hc, favorableProjection, hz]
      have hsub : (Finset.univ.filter (fun i => mixBids cy (favorableProjection h b z) i = h)) ⊆
          Finset.univ.filter (fun i => mixBids cy z i = h) := by
        intro i hi
        have he := (Finset.mem_filter.mp hi).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        by_cases hc : (cy i).1 = true
        · simpa [mixBids, hc] using he
        · have hz : z i ≤ h := by simpa [mixBids, hc] using hw i
          have he' : h - 1 = h := by simpa [mixBids, hc, favorableProjection, hz] using he
          linarith
      have hc : ((Finset.univ.filter (fun i => mixBids cy (favorableProjection h b z) i = h)).card : ℝ) ≤
          ((Finset.univ.filter (fun i => mixBids cy z i = h)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      simp only [payoff, if_pos hw, if_pos hw']
      exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    · rw [payoff, if_neg hw]
      exact payoff_nonnegative v h (hhb.le.trans hbv) _
  have hlo : payoff v b (mixBids cy (favorableProjection h b z)) ≤ payoff v b (mixBids cy z) := by
    by_cases hw : ∀ i, mixBids cy (favorableProjection h b z) i ≤ b
    · have hw' : ∀ i, mixBids cy z i ≤ b := by
        intro i
        have hi := hw i
        by_cases hc : (cy i).1 = true
        · simpa [mixBids, hc] using hi
        · by_cases hz : z i ≤ h
          · simp only [mixBids, if_neg hc]
            exact hz.trans hhb.le
          · have hi' : b + 1 ≤ b := by simpa [mixBids, hc, favorableProjection, hz] using hi
            linarith
      have heq : (Finset.univ.filter (fun i => mixBids cy (favorableProjection h b z) i = b)) =
          Finset.univ.filter (fun i => mixBids cy z i = b) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hc : (cy i).1 = true
        · simp [mixBids, hc]
        · by_cases hz : z i ≤ h
          · simp only [mixBids, if_neg hc, favorableProjection, if_pos hz]
            constructor <;> intro he <;> linarith
          · have hi := hw i
            simp only [mixBids, favorableProjection, if_neg hc, if_neg hz] at hi
            linarith
      simp only [payoff, if_pos hw, if_pos hw', heq]
      exact le_rfl
    · rw [payoff, if_neg hw]
      exact payoff_nonnegative v b hbv _
  exact sub_le_sub hup hlo

lemma heterogeneous_payoff (m : ℕ) (μ : Fin m → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (v b : ℝ) (hμ : ∀ i, μ i {b} = 0) :
    expUtil v b (Measure.pi μ) = (∏ i, (μ i (Set.Iio b)).toReal) * (v-b) := by
  classical
  let S : Set (Fin m → ℝ) := Set.univ.pi (fun _ => Set.Iio b)
  have hs : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Iio)
  have hn : ∀ᵐ o ∂Measure.pi μ, ∀ i, o i ≠ b := by
    rw [ae_all_iff]
    intro i
    apply ae_iff.mpr
    simpa only [not_not, Set.preimage, Set.mem_singleton_iff, Function.eval] using
      (Measure.pi_eval_preimage_null μ (i := i) (hμ i))
  have he : (fun o => payoff v b o) =ᵐ[Measure.pi μ] S.indicator (fun _ => v-b) := by
    filter_upwards [hn] with o ho
    by_cases hw : ∀ i, o i ≤ b
    · have hm : o ∈ S := by
        simpa [S, Set.mem_pi] using (fun i => lt_of_le_of_ne (hw i) (ho i))
      have hf : (Finset.univ.filter (fun i => o i = b)) = ∅ := by
        ext i
        simp [ho i]
      simp [payoff, hw, hf, Set.indicator_of_mem hm]
    · have hm : o ∉ S := by
        intro h
        have hh : ∀ i, o i < b := by simpa [S, Set.mem_pi] using h
        exact hw (fun i => (hh i).le)
      simp [payoff, hw, Set.indicator_of_notMem hm]
  unfold expUtil
  rw [integral_congr_ae he, integral_indicator_const _ hs]
  simp only [Measure.real, S, Measure.pi_pi, ENNReal.toReal_prod, smul_eq_mul]

lemma fixed_product (m : ℕ) (τ : ℝ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (z : Fin m → ℝ) :
    (constrainedLaw m τ G).map (fun cy => mixBids cy z) = Measure.pi (fun i =>
      Real.toNNReal τ • G + Real.toNNReal (1-τ) • Measure.dirac (z i)) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  unfold constrainedLaw mixBids
  have hm (i : Fin m) : Measurable (fun p : Bool × ℝ => if p.1 then p.2 else z i) :=
    Measurable.ite (by measurability) measurable_snd measurable_const
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [component_law]

lemma fixed_utility (m : ℕ) (τ L v b : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) (z : Fin m → ℝ) (hzb : ∀ i, z i ≠ b) :
    (∫ cy, payoff v b (mixBids cy z) ∂constrainedLaw m τ (uniformG L v)) =
      (∏ i, (τ * ((b-L)/(v-L)) + if z i < b then 1-τ else 0)) * (v-b) := by
  letI := uniform_probability L v hLv
  have hm : Measurable (fun cy : Fin m → Bool × ℝ => mixBids cy z) := by
    apply measurable_pi_lambda
    intro i
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  have he : (∫ cy, payoff v b (mixBids cy z) ∂constrainedLaw m τ (uniformG L v)) =
      expUtil v b ((constrainedLaw m τ (uniformG L v)).map (fun cy => mixBids cy z)) := by
    unfold expUtil
    exact (integral_map_of_stronglyMeasurable hm (payoff_measurable m v b).stronglyMeasurable).symm
  rw [he, fixed_product, heterogeneous_payoff _ _ _ _ (fun i => common_no_tie τ L v b (z i) (hzb i))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, uniform_Iio L v b hLv hLb hbv]
  have hratio : 0 ≤ (b-L)/(v-L) := div_nonneg (sub_nonneg.mpr hLb) (sub_pos.mpr hLv).le
  simp [ENNReal.toReal_ofReal hratio, Real.toNNReal_of_nonneg hτ0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hτ1), Measure.dirac_apply']
  by_cases hz : z i < b <;> simp [Set.indicator, hz]

lemma fixed_integrable (m : ℕ) (τ L v b : ℝ) (z : Fin m → ℝ) :
    Integrable (fun cy => payoff v b (mixBids cy z)) (constrainedLaw m τ (uniformG L v)) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  letI : IsFiniteMeasure (constrainedLaw m τ (uniformG L v)) := by
    unfold constrainedLaw; infer_instance
  have hm : Measurable (fun cy : Fin m → Bool × ℝ => mixBids cy z) := by
    apply measurable_pi_lambda
    intro i
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  apply Integrable.mono' (integrable_const |v-b|)
    ((payoff_measurable m v b).comp hm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun cy => payoff_bound m v b (mixBids cy z))

lemma fixed_downward_gain (m : ℕ) (τ L v h b : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hLv : L < v) (hLh : L ≤ h) (hhb : h < b) (hbv : b ≤ v) (z : Fin m → ℝ) :
    (∫ cy, payoff v h (mixBids cy z) ∂constrainedLaw m τ (uniformG L v)) -
      (∫ cy, payoff v b (mixBids cy z) ∂constrainedLaw m τ (uniformG L v)) ≤
        max ((v-h) * (1-τ+τ*((h-L)/(v-L))) ^ m -
          (v-b) * (1-τ+τ*((b-L)/(v-L))) ^ m) 0 := by
  classical
  let z' := favorableProjection h b z
  let low : Fin m → Bool := fun i => decide (z i ≤ h)
  have hhne : ∀ i, z' i ≠ h := by
    intro i
    dsimp [z', favorableProjection]
    split_ifs <;> linarith
  have hbne : ∀ i, z' i ≠ b := by
    intro i
    dsimp [z', favorableProjection]
    split_ifs <;> linarith
  have hhif (i : Fin m) : (if z' i < h then 1-τ else 0) =
      (if low i then 1-τ else 0) := by
    by_cases hi : z i ≤ h
    · simp [z', favorableProjection, hi, low, show h-1 < h by linarith]
    · simp [z', favorableProjection, hi, low, show ¬ b+1 < h by linarith]
  have hbif (i : Fin m) : (if z' i < b then 1-τ else 0) =
      (if low i then 1-τ else 0) := by
    by_cases hi : z i ≤ h
    · simp [z', favorableProjection, hi, low, show h-1 < b by linarith]
    · simp [z', favorableProjection, hi, low, show ¬ b+1 < b by linarith]
  have hmono := integral_mono
    ((fixed_integrable m τ L v h z).sub (fixed_integrable m τ L v b z))
    ((fixed_integrable m τ L v h z').sub (fixed_integrable m τ L v b z'))
    (fun cy => projected_gain_upper v h b hhb hbv cy z)
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (fixed_integrable m τ L v h z) (fixed_integrable m τ L v b z),
    integral_sub (fixed_integrable m τ L v h z') (fixed_integrable m τ L v b z')] at hmono
  apply hmono.trans
  rw [fixed_utility m τ L v h hτ0 hτ1.le hLv hLh (hhb.le.trans hbv) z' hhne,
    fixed_utility m τ L v b hτ0 hτ1.le hLv (hLh.trans hhb.le) hbv z' hbne]
  simp_rw [hhif, hbif]
  have hp : 0 ≤ (h-L)/(v-L) := div_nonneg (sub_nonneg.mpr hLh) (sub_pos.mpr hLv).le
  have hpq : (h-L)/(v-L) ≤ (b-L)/(v-L) :=
    (div_le_div_iff_of_pos_right (sub_pos.mpr hLv)).mpr (by linarith)
  have hb := binary_product_gain_bound low τ ((h-L)/(v-L)) ((b-L)/(v-L)) (v-h) (v-b)
    hτ0 hτ1 hp hpq (by linarith)
  simpa only [Fintype.card_fin, mul_comm] using hb

lemma arbitrary_downward_gain (n : ℕ) (τ L v h b : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hLv : L < v) (hLh : L ≤ h) (hhb : h < b) (hbv : b ≤ v)
    (H : Measure (Fin (n-1) → ℝ)) [IsProbabilityMeasure H] :
    expUtil v h (envOf n τ (uniformG L v) H) -
      expUtil v b (envOf n τ (uniformG L v) H) ≤
        max (uPlus n τ L v h - uPlus n τ L v b) 0 := by
  letI := bern_probability τ hτ0 hτ1.le
  letI := uniform_probability L v hLv
  letI : IsProbabilityMeasure (constrainedLaw (n-1) τ (uniformG L v)) := by
    unfold constrainedLaw; infer_instance
  let μ := (constrainedLaw (n-1) τ (uniformG L v)).prod H
  have hih := mixed_integrable v h (fun p => mixBids p.1 p.2) measurable_mix μ
  have hib := mixed_integrable v b (fun p => mixBids p.1 p.2) measurable_mix μ
  have hfub := integral_prod_symm _ (hih.sub hib)
  simp only [Pi.sub_apply] at hfub
  rw [environment_integral, environment_integral, ← integral_sub hih hib, hfub]
  have hh := integral_mono (hih.sub hib).integral_prod_right
    (integrable_const (max (uPlus n τ L v h - uPlus n τ L v b) 0)) (fun z => by
      change (∫ cy, payoff v h (mixBids cy z) - payoff v b (mixBids cy z)
        ∂constrainedLaw (n-1) τ (uniformG L v)) ≤ _
      rw [integral_sub (fixed_integrable (n-1) τ L v h z) (fixed_integrable (n-1) τ L v b z)]
      simpa only [uPlus] using fixed_downward_gain (n-1) τ L v h b hτ0 hτ1 hLv hLh hhb hbv z)
  simp only [Pi.sub_apply, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hh
  convert hh using 1 <;> rfl

lemma admissible_downward_gain (n : ℕ) (τ L v h b : ℝ) (hτ1 : τ < 1)
    (hLv : L < v) (hLh : L ≤ h) (hhb : h ≤ b) (hbv : b ≤ v)
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L (uniformG L v)) :
    expUtil v h B - expUtil v b B ≤ tooHigh n τ L v b := by
  have hLb : L ≤ b := hLh.trans hhb
  have hc : Continuous (uPlus n τ L v) := by unfold uPlus; fun_prop
  have hbounded : BddAbove (uPlus n τ L v '' Set.Icc L b) :=
    (isCompact_Icc.image hc).bddAbove
  have hself : uPlus n τ L v b ≤ sSup (uPlus n τ L v '' Set.Icc L b) :=
    le_csSup hbounded ⟨b, ⟨hLb, le_rfl⟩, rfl⟩
  have hzero : 0 ≤ tooHigh n τ L v b := sub_nonneg.mpr hself
  by_cases he : h = b
  · simpa only [he, sub_self] using hzero
  have hstrict : h < b := lt_of_le_of_ne hhb he
  have hbound : uPlus n τ L v h - uPlus n τ L v b ≤ tooHigh n τ L v b :=
    sub_le_sub_right (le_csSup hbounded ⟨h, ⟨hLh, hhb⟩, rfl⟩) _
  rcases hB with ⟨_, _, hτ0, _, _, _, H, hH, _, rfl⟩
  letI := hH
  exact (arbitrary_downward_gain n τ L v h b hτ0 hτ1 hLv hLh hstrict hbv H).trans
    (max_le hbound hzero)

lemma admissible_lower_support (n : ℕ) (τ L : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L G) :
    ∀ᵐ o ∂B, ∀ i, L ≤ o i := by
  rcases hB with ⟨_, _, hτ0, hτ1, hG, hGL, H, hH, hHL, rfl⟩
  letI := hG
  letI := hH
  letI := bern_probability τ hτ0 hτ1
  have hga : ∀ᵐ y ∂G, L ≤ y := by
    apply ae_iff.mpr
    simpa [Set.Iio, not_le] using hGL
  have hp : ∀ᵐ y : Bool × ℝ ∂(bern τ).prod G, L ≤ y.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    exact Filter.Eventually.of_forall (fun _ => hga)
  have hcy : ∀ᵐ cy ∂constrainedLaw (n-1) τ G, ∀ i, L ≤ (cy i).2 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n-1) => (bern τ).prod G)
      (i := i)).eventually hp
  have hz : ∀ᵐ z ∂H, ∀ i, L ≤ z i :=
    (mem_ae_iff_prob_eq_one (by measurability)).mpr hHL
  have hS : MeasurableSet {o : Fin (n-1) → ℝ | ∀ i, L ≤ o i} := by measurability
  unfold envOf
  apply (ae_map_iff measurable_mix.aemeasurable hS).mpr
  apply (Measure.ae_prod_iff_ae_ae (hS.preimage measurable_mix)).mpr
  filter_upwards [hcy] with cy hcy
  filter_upwards [hz] with z hz
  intro i
  simp only [mixBids]
  split_ifs
  · exact hcy i
  · exact hz i

lemma utility_below_floor (n : ℕ) (hn : 2 ≤ n) (τ L v h : ℝ) (hhL : h < L)
    (G : Measure ℝ) [IsFiniteMeasure G]
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L G) :
    expUtil v h B = 0 := by
  have hz : (fun o => payoff v h o) =ᵐ[B] fun _ => 0 := by
    filter_upwards [admissible_lower_support n τ L G B hB] with o ho
    have hnwin : ¬ ∀ i, o i ≤ h := by
      intro hw
      let i : Fin (n-1) := ⟨0, by omega⟩
      exact (not_le_of_gt hhL) ((ho i).trans (hw i))
    simp [payoff, hnwin]
  unfold expUtil
  rw [integral_congr_ae hz, integral_zero]

lemma utility_nonnegative (m : ℕ) (v b : ℝ) (hbv : b ≤ v)
    (B : Measure (Fin m → ℝ)) : 0 ≤ expUtil v b B := by
  apply integral_nonneg
  intro o
  unfold payoff
  split_ifs
  · apply div_nonneg (sub_nonneg.mpr hbv)
    positivity
  · exact le_rfl

lemma utility_above_value (m : ℕ) (v h : ℝ) (hvh : v ≤ h)
    (B : Measure (Fin m → ℝ)) : expUtil v h B ≤ 0 := by
  apply integral_nonpos
  intro o
  unfold payoff
  split_ifs
  · apply div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hvh)
    positivity
  · exact le_rfl

lemma uPlus_ray_bound (n : ℕ) (τ L v h : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLh : L ≤ h) : uPlus n τ L v h ≤ v-L := by
  have hp0 : 0 ≤ (h-L)/(v-L) := div_nonneg (sub_nonneg.mpr hLh) (sub_pos.mpr hLv).le
  have ha0 : 0 ≤ 1-τ+τ*((h-L)/(v-L)) := by positivity
  unfold uPlus
  by_cases hhv : h ≤ v
  · have hp1 : (h-L)/(v-L) ≤ 1 := (div_le_one (sub_pos.mpr hLv)).mpr (by linarith)
    have ha1 : 1-τ+τ*((h-L)/(v-L)) ≤ 1 := by nlinarith
    have hpow : (1-τ+τ*((h-L)/(v-L)))^(n-1) ≤ 1 := pow_le_one₀ ha0 ha1
    calc
      (v-h) * (1-τ+τ*((h-L)/(v-L)))^(n-1) ≤ (v-h)*1 :=
        mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hhv)
      _ ≤ v-L := by linarith
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg ha0 _)).trans
      (sub_pos.mpr hLv).le

lemma all_deviations_upper (n : ℕ) (hn : 2 ≤ n) (τ L v b h : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v)
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L (uniformG L v)) :
    expUtil v h B - expUtil v b B ≤ max (tooHigh n τ L v b) (tooLow n τ L v b) := by
  have hnonneg : 0 ≤ tooHigh n τ L v b := by
    have hc : Continuous (uPlus n τ L v) := by unfold uPlus; fun_prop
    exact sub_nonneg.mpr (le_csSup (isCompact_Icc.image hc).bddAbove ⟨b, ⟨hLb, le_rfl⟩, rfl⟩)
  have hz : 0 ≤ max (tooHigh n τ L v b) (tooLow n τ L v b) :=
    hnonneg.trans (le_max_left _ _)
  by_cases hLh : L ≤ h
  · by_cases hhv : h ≤ v
    · by_cases hhb : h ≤ b
      · exact (admissible_downward_gain n τ L v h b hτ1 hLv hLh hhb hbv B hB).trans
          (le_max_left _ _)
      · have hbounded : BddAbove (uPlus n τ L v '' Set.Ioi b) := by
          refine ⟨v-L, ?_⟩
          rintro _ ⟨y, hy, rfl⟩
          exact uPlus_ray_bound n τ L v y hτ0.le hτ1.le hLv (hLb.trans hy.le)
        have hu : uPlus n τ L v h - uMinus n τ L v b ≤ tooLow n τ L v b :=
          sub_le_sub_right (le_csSup hbounded ⟨h, lt_of_not_ge hhb, rfl⟩) _
        exact (deviation_upper n τ L v b h hLv hLb hbv hLh hhv B hB).trans
          (hu.trans (le_max_right _ _))
    · exact (sub_nonpos.mpr ((utility_above_value (n-1) v h (le_of_not_ge hhv) B).trans
        (utility_nonnegative (n-1) v b hbv B))).trans hz
  · rw [utility_below_floor n hn τ L v h (lt_of_not_ge hLh) (uniformG L v) B hB]
    exact (sub_nonpos.mpr (utility_nonnegative (n-1) v b hbv B)).trans hz

lemma maximal_loss_upper (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) :
    maxLoss v b (varBidSet n τ L (uniformG L v)) ≤ max (tooHigh n τ L v b) (tooLow n τ L v b) := by
  unfold maxLoss
  apply csSup_le
  · exact ⟨loss v b (commonBidEnv n τ (uniformG L v) L),
      commonBidEnv n τ (uniformG L v) L,
      common_admissible n hn τ L v hτ0 hτ1 hL hLv L le_rfl, rfl⟩
  · rintro _ ⟨B, hB, rfl⟩
    unfold loss
    apply sub_le_iff_le_add.mpr
    apply csSup_le
    · exact ⟨expUtil v 0 B, 0, by simp, rfl⟩
    · rintro _ ⟨h, _, rfl⟩
      exact sub_le_iff_le_add.mp (all_deviations_upper n hn τ L v b h hτ0 hτ1 hLv hLb hbv B hB)

end RobustFPA.VarBid

open AcceptedMinimax.RobustFPA.VarBid

open RobustFPA.VarBid in
theorem RobustFPA.VarBid.maxLoss_formula (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hL : 0 ≤ L) (hLv : L < v) (b : ℝ) (hLb : L ≤ b) (hbv : b ≤ v) :
    maxLoss v b (varBidSet n τ L (uniformG L v)) = max (tooHigh n τ L v b) (tooLow n τ L v b) := by
  exact le_antisymm (maximal_loss_upper n hn τ L v b hτ0 hτ1 hL hLv hLb hbv)
    (analytic_max_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb hbv)

namespace RobustBidResearch

lemma base_pos (τ L v b : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hLv : L < v) (hb : L ≤ b) : 0 < 1-τ+τ*((b-L)/(v-L)) := by
  have hp := mul_nonneg hτ0.le (div_nonneg (sub_nonneg.mpr hb) (sub_pos.mpr hLv).le)
  linarith

lemma plus_cont (n : ℕ) (τ L v : ℝ) : Continuous (uPlus n τ L v) := by
  unfold uPlus
  fun_prop

lemma plus_deriv (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hLv : L < v) :
    HasDerivAt (uPlus n τ L v)
      ((1-τ+τ*((b-L)/(v-L)))^(n-2) * ((n:ℝ)*τ/(v-L)) * (bTilde n τ L v-b)) b := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+2 := ⟨n-2,by omega⟩
  have hnum : (k:ℝ)+2 ≠ 0 := by positivity
  have hd : v-L ≠ 0 := ne_of_gt (sub_pos.mpr hLv)
  have ht : τ ≠ 0 := ne_of_gt hτ0
  have ha : HasDerivAt (fun z : ℝ => 1-τ+τ*((z-L)/(v-L))) (τ/(v-L)) b := by
    convert (hasDerivAt_const b (1-τ)).add ((((hasDerivAt_id b).sub_const L).div_const (v-L)).const_mul τ) using 1 <;> first | rfl | ring
  have h := ((hasDerivAt_const b v).sub (hasDerivAt_id b)).mul (ha.pow (k+1))
  unfold uPlus bTilde
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  convert h using 1 <;> try rfl
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply,Pi.sub_apply,id_eq,pow_succ]
  field_simp [hd,ht,hnum]
  <;> ring

lemma plus_maximum (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    IsMaxOn (uPlus n τ L v) (Ici L) (max (bTilde n τ L v) L) := by
  have hc := plus_cont n τ L v
  have hp : 0 ≤ (n:ℝ)*τ/(v-L) := div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le
  apply isMaxOn_Ici_of_deriv hc.continuousAt hc.continuousAt
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    have hbt : b < bTilde n τ L v := by
      rcases lt_max_iff.mp hb.2 with h | h
      · exact h
      · linarith [hb.1]
    exact mul_nonneg (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hb.1.le).le _) hp)
      (sub_nonneg.mpr hbt.le)
  · intro b hb
    have hbt : bTilde n τ L v ≤ b := (le_max_left _ _).trans hb.le
    have hLb : L ≤ b := (le_max_right _ _).trans hb.le
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hLb).le _) hp)
      (sub_nonpos.mpr hbt)

lemma peak_bounds (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hLv : L < v) : L ≤ peakBid n τ L v ∧ peakBid n τ L v < v := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have htilde : bTilde n τ L v < v := by
    unfold bTilde
    exact sub_lt_self _ (div_pos (sub_pos.mpr hLv) (mul_pos hn0 hτ0))
  exact ⟨le_max_left _ _,max_lt hLv htilde⟩

lemma gap_cont (n : ℕ) (τ L v : ℝ) : Continuous (fun b => uPlus n τ L v b-uMinus n τ L v b) := by
  unfold uPlus uMinus
  fun_prop

lemma gap_deriv (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ) (hLv : L < v) :
    HasDerivAt (fun z => uPlus n τ L v z-uMinus n τ L v z)
      (((1-τ+τ*((b-L)/(v-L)))^(n-2)-(τ*((b-L)/(v-L)))^(n-2)) *
      ((n:ℝ)*τ*(v-b)/(v-L)-1)-(1-τ)*(τ*((b-L)/(v-L)))^(n-2)) b := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+2 := ⟨n-2,by omega⟩
  have ha : HasDerivAt (fun z : ℝ => 1-τ+τ*((z-L)/(v-L))) (τ/(v-L)) b := by
    convert (hasDerivAt_const b (1-τ)).add ((((hasDerivAt_id b).sub_const L).div_const (v-L)).const_mul τ) using 1 <;> first | rfl | ring
  have hd : HasDerivAt (fun z : ℝ => τ*((z-L)/(v-L))) (τ/(v-L)) b := by
    convert (((hasDerivAt_id b).sub_const L).div_const (v-L)).const_mul τ using 1 <;> first | rfl | ring
  have hv := (hasDerivAt_const b v).sub (hasDerivAt_id b)
  have hh := (hv.mul (ha.pow (k+1))).sub ((hd.pow (k+1)).mul hv)
  unfold uPlus uMinus
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  convert hh using 1 <;> try rfl
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply,Pi.sub_apply,id_eq,pow_succ]
  field_simp [ne_of_gt (sub_pos.mpr hLv)]
  <;> ring

lemma plus_anti (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    AntitoneOn (uPlus n τ L v) (Icc (peakBid n τ L v) v) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (plus_cont n τ L v).continuousOn
  · intro b hb;exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Icc] at hb
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    have hLb : L ≤ b := (le_max_left L (bTilde n τ L v)).trans hb.1.le
    have htb : bTilde n τ L v ≤ b := (le_max_right L _).trans hb.1.le
    apply mul_nonpos_of_nonneg_of_nonpos _ (sub_nonpos.mpr htb)
    exact mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hLb).le _)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le)

lemma gap_strict (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    StrictAntiOn (fun b => uPlus n τ L v b-uMinus n τ L v b) (Icc (peakBid n τ L v) v) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (gap_cont n τ L v).continuousOn
  intro b hb
  rw [interior_Icc] at hb
  rw [(gap_deriv n hn τ L v b hLv).deriv]
  have hLb : L < b := (le_max_left L (bTilde n τ L v)).trans_lt hb.1
  have htb : bTilde n τ L v ≤ b := (le_max_right L _).trans hb.1.le
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hp : 0 < τ*((b-L)/(v-L)) := mul_pos hτ0 (div_pos (sub_pos.mpr hLb) (sub_pos.mpr hLv))
  have hab : τ*((b-L)/(v-L)) ≤ 1-τ+τ*((b-L)/(v-L)) := by linarith
  have hpow := pow_le_pow_left₀ hp.le hab (n-2)
  have hR : (n:ℝ)*τ*(v-b)/(v-L) ≤ 1 := by
    have hh : v-b ≤ (v-L)/((n:ℝ)*τ) := by dsimp [bTilde] at htb;linarith
    have hh' := (le_div_iff₀ (mul_pos hn0 hτ0)).mp hh
    apply (div_le_iff₀ (sub_pos.mpr hLv)).2
    nlinarith only [hh']
  have hfirst := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpow) (sub_nonpos.mpr hR)
  have hlast := mul_pos (sub_pos.mpr hτ1) (pow_pos hp (n-2))
  linarith only [hfirst,hlast]

lemma plus_max (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (b : ℝ) (hb : L ≤ b) :
    uPlus n τ L v b ≤ uPlus n τ L v (peakBid n τ L v) := by
  have h := plus_maximum n hn τ L v hτ0 hτ1 hLv hb
  simpa [peakBid,max_comm] using h

lemma plus_mono_before (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    MonotoneOn (uPlus n τ L v) (Icc L (peakBid n τ L v)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (plus_cont n τ L v).continuousOn
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Icc] at hb
    have hbt : b < bTilde n τ L v := by
      rcases lt_max_iff.mp hb.2 with h | h
      · linarith [hb.1]
      · exact h
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    exact mul_nonneg (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hb.1.le).le _)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le))
      (sub_nonneg.mpr hbt.le)

lemma plus_anti_after (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    AntitoneOn (uPlus n τ L v) (Ici (peakBid n τ L v)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (plus_cont n τ L v).continuousOn
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Ici] at hb
    have hLb : L ≤ b := (le_max_left _ _).trans hb.le
    have htb : bTilde n τ L v ≤ b := (le_max_right _ _).trans hb.le
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hLb).le _)
        (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le))
      (sub_nonpos.mpr htb)

lemma right_sup_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (hb : L ≤ b) :
    uPlus n τ L v b ≤ sSup (uPlus n τ L v '' Ioi b) := by
  have hbd : BddAbove (uPlus n τ L v '' Ioi b) := by
    refine ⟨uPlus n τ L v (peakBid n τ L v),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact plus_max n hn τ L v hτ0 hτ1 hLv x (hb.trans hx.le)
  exact ContinuousWithinAt.closure_le (by simp) (plus_cont n τ L v).continuousAt.continuousWithinAt
    continuousWithinAt_const (fun x hx => le_csSup hbd ⟨x,hx,rfl⟩)

lemma formulas_after (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (hb : peakBid n τ L v ≤ b) :
    tooHigh n τ L v b = uPlus n τ L v (peakBid n τ L v)-uPlus n τ L v b ∧
    tooLow n τ L v b = uPlus n τ L v b-uMinus n τ L v b := by
  have hLb : L ≤ b := (le_max_left _ _).trans hb
  have hmax := plus_max n hn τ L v hτ0 hτ1 hLv
  have hs1 : sSup (uPlus n τ L v '' Icc L b) = uPlus n τ L v (peakBid n τ L v) := by
    apply le_antisymm
    · apply csSup_le (s := uPlus n τ L v '' Icc L b) ⟨uPlus n τ L v L, L, ⟨le_rfl,hLb⟩,rfl⟩
      rintro _ ⟨x,hx,rfl⟩
      exact hmax x hx.1
    · apply le_csSup (s := uPlus n τ L v '' Icc L b) ⟨uPlus n τ L v (peakBid n τ L v),?_⟩ ⟨peakBid n τ L v,⟨le_max_left _ _,hb⟩,rfl⟩
      rintro _ ⟨x,hx,rfl⟩
      exact hmax x hx.1
  have hs2 : sSup (uPlus n τ L v '' Ioi b) = uPlus n τ L v b := by
    apply le_antisymm
    · apply csSup_le (s := uPlus n τ L v '' Ioi b) ⟨uPlus n τ L v (b+1),b+1,by simp,rfl⟩
      rintro _ ⟨x,hx,rfl⟩
      exact plus_anti_after n hn τ L v hτ0 hτ1 hLv hb (hb.trans hx.le) hx.le
    · exact right_sup_bound n hn τ L v b hτ0 hτ1 hLv hLb
  exact ⟨by rw [tooHigh,hs1],by rw [tooLow,hs2]⟩

lemma gap_pos (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (hLb : L ≤ b) (hbv : b < v) :
    uMinus n τ L v b < uPlus n τ L v b := by
  have hp : 0 ≤ τ*((b-L)/(v-L)) := mul_nonneg hτ0.le
    (div_nonneg (sub_nonneg.mpr hLb) (sub_pos.mpr hLv).le)
  have hpow := pow_lt_pow_left₀ (by linarith : τ*((b-L)/(v-L)) < 1-τ+τ*((b-L)/(v-L))) hp
    (by omega : n-1 ≠ 0)
  have h := mul_lt_mul_of_pos_left hpow (sub_pos.mpr hbv)
  simpa [uMinus,uPlus,mul_comm] using h

end RobustBidResearch

theorem accepted_unique (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    MonotoneOn (fun b => uPlus n τ L v (peakBid n τ L v)-uPlus n τ L v b)
      (Icc (peakBid n τ L v) v) ∧
    StrictAntiOn (fun b => uPlus n τ L v b-uMinus n τ L v b) (Icc (peakBid n τ L v) v) ∧
    ∃! b : ℝ, peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b := by
  have hb := RobustBidResearch.peak_bounds n hn τ L v hτ0 hLv
  have ha := RobustBidResearch.plus_anti n hn τ L v hτ0 hτ1 hLv
  have hs := RobustBidResearch.gap_strict n hn τ L v hτ0 hτ1 hLv
  have hm : MonotoneOn (fun b => uPlus n τ L v (peakBid n τ L v)-uPlus n τ L v b)
      (Icc (peakBid n τ L v) v) := by
    intro a ha' b hb' hab
    exact sub_le_sub_left (ha ha' hb' hab) _
  refine ⟨hm,hs,?_⟩
  let F : ℝ → ℝ := fun b => uPlus n τ L v (peakBid n τ L v)-uPlus n τ L v b-
    (uPlus n τ L v b-uMinus n τ L v b)
  have hfc : Continuous F := by
    dsimp [F]
    exact (continuous_const.sub (RobustBidResearch.plus_cont n τ L v)).sub (RobustBidResearch.gap_cont n τ L v)
  have hlow : F (peakBid n τ L v) ≤ 0 := by
    have hd : 0 ≤ τ*((peakBid n τ L v-L)/(v-L)) :=
      mul_nonneg hτ0.le (div_nonneg (sub_nonneg.mpr hb.1) (sub_pos.mpr hLv).le)
    have hp := pow_le_pow_left₀ hd (by linarith :
      τ*((peakBid n τ L v-L)/(v-L)) ≤ 1-τ+τ*((peakBid n τ L v-L)/(v-L))) (n-1)
    have hh := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hb.2.le)
    dsimp [F,uPlus,uMinus]
    nlinarith only [hh]
  have hhigh : 0 ≤ F v := by
    have hp := RobustBidResearch.base_pos τ L v (peakBid n τ L v) hτ0 hτ1 hLv hb.1
    dsimp [F,uPlus,uMinus]
    simp only [sub_self,zero_mul,mul_zero,sub_zero]
    exact mul_nonneg (sub_nonneg.mpr hb.2.le) (pow_nonneg hp.le _)
  obtain ⟨b,hbi,hbF⟩ := intermediate_value_Icc hb.2.le hfc.continuousOn ⟨hlow,hhigh⟩
  have heq : Equation3 n τ L v b := by
    dsimp [F] at hbF
    exact sub_eq_zero.mp hbF
  refine ⟨b,⟨hbi.1,hbi.2,heq⟩,?_⟩
  intro z hz
  have hzi : z ∈ Icc (peakBid n τ L v) v := ⟨hz.1,hz.2.1⟩
  have hzE := hz.2.2
  unfold Equation3 at heq hzE
  rcases lt_trichotomy z b with h | h | h
  · have h1 := hm hzi hbi h.le
    have h2 := hs hzi hbi h
    linarith
  · exact h
  · have h1 := hm hbi hzi h.le
    have h2 := hs hbi hzi h
    linarith

theorem RobustFPA.VarBid.equalizerSet_eq (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    equalizerSet n τ L v = {b | peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b} := by
  ext b
  constructor
  · rintro ⟨⟨hLb,hbv⟩,heq⟩
    have hpb : peakBid n τ L v ≤ b := by
      by_contra h
      have hbp := lt_of_not_ge h
      have hhigh : tooHigh n τ L v b = 0 := by
        have hm := RobustBidResearch.plus_mono_before n hn τ L v hτ0 hτ1 hLv
        have hs : sSup (uPlus n τ L v '' Icc L b) = uPlus n τ L v b := by
          apply le_antisymm
          · apply csSup_le (s := uPlus n τ L v '' Icc L b) ⟨uPlus n τ L v b,b,⟨hLb,le_rfl⟩,rfl⟩
            rintro _ ⟨x,hx,rfl⟩
            exact hm ⟨hx.1,hx.2.trans hbp.le⟩ ⟨hLb,hbp.le⟩ hx.2
          · apply le_csSup (s := uPlus n τ L v '' Icc L b) ⟨uPlus n τ L v b,?_⟩ ⟨b,⟨hLb,le_rfl⟩,rfl⟩
            rintro _ ⟨x,hx,rfl⟩
            exact hm ⟨hx.1,hx.2.trans hbp.le⟩ ⟨hLb,hbp.le⟩ hx.2
        rw [tooHigh,hs,sub_self]
      have hbound := RobustBidResearch.right_sup_bound n hn τ L v b hτ0 hτ1 hLv hLb
      have hpos := RobustBidResearch.gap_pos n hn τ L v b hτ0 hτ1 hLv hLb
        (hbp.trans (RobustBidResearch.peak_bounds n hn τ L v hτ0 hLv).2)
      rw [hhigh] at heq
      unfold tooLow at heq
      linarith
    have hh := RobustBidResearch.formulas_after n hn τ L v b hτ0 hτ1 hLv hpb
    exact ⟨hpb,hbv,by dsimp [Equation3];rw [hh.1,hh.2] at heq;exact heq⟩
  · rintro ⟨hpb,hbv,heq⟩
    have hh := RobustBidResearch.formulas_after n hn τ L v b hτ0 hτ1 hLv hpb
    exact ⟨⟨(le_max_left _ _).trans hpb,hbv⟩,by rw [hh.1,hh.2];exact heq⟩

namespace RobustBidResearch

lemma plus_strict_after (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    StrictAntiOn (uPlus n τ L v) (Set.Icc (peakBid n τ L v) v) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (plus_cont n τ L v).continuousOn
  intro b hb
  rw [interior_Icc] at hb
  rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
  have hLb : L ≤ b := (le_max_left L (bTilde n τ L v)).trans hb.1.le
  have htb : bTilde n τ L v < b := (le_max_right L _).trans_lt hb.1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  exact mul_neg_of_pos_of_neg
    (mul_pos (pow_pos (base_pos τ L v b hτ0 hτ1 hLv hLb) _)
      (div_pos (mul_pos hn0 hτ0) (sub_pos.mpr hLv))) (sub_neg.mpr htb)

lemma minus_deriv (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ) (hLv : L < v) :
    HasDerivAt (uMinus n τ L v)
      ((τ*((b-L)/(v-L)))^(n-2) * (τ/(v-L)) * ((n:ℝ)*(v-b)-(v-L))) b := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+2 := ⟨n-2,by omega⟩
  have hd : HasDerivAt (fun z : ℝ => τ*((z-L)/(v-L))) (τ/(v-L)) b := by
    convert (((hasDerivAt_id b).sub_const L).div_const (v-L)).const_mul τ using 1 <;> first | rfl | ring
  have hh := (hd.pow (k+1)).mul ((hasDerivAt_const b v).sub (hasDerivAt_id b))
  unfold uMinus
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  convert hh using 1 <;> try rfl
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply,Pi.sub_apply,id_eq,pow_succ]
  field_simp [ne_of_gt (sub_pos.mpr hLv)]
  <;> ring

lemma minus_mono_before (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    MonotoneOn (uMinus n τ L v) (Set.Icc L (peakBid n τ L v)) := by
  have hc : Continuous (uMinus n τ L v) := by unfold uMinus; fun_prop
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc.continuousOn
  · intro b hb
    exact (minus_deriv n hn τ L v b hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Icc] at hb
    rw [(minus_deriv n hn τ L v b hLv).deriv]
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have htb : b < bTilde n τ L v := by
      rcases lt_max_iff.mp hb.2 with h | h
      · exact False.elim (lt_asymm hb.1 h)
      · exact h
    have hdist : (v-L)/((n:ℝ)*τ) < v-b := by dsimp [bTilde] at htb; linarith
    have hm := (div_lt_iff₀ (mul_pos hn0 hτ0)).mp hdist
    have hlow : 0 ≤ (n:ℝ)*(v-b)-(v-L) := by
      have hbv := htb.trans (lt_of_lt_of_le (by
        exact sub_lt_self v (div_pos (sub_pos.mpr hLv) (mul_pos hn0 hτ0))) le_rfl)
      nlinarith [mul_pos hn0 (sub_pos.mpr hbv)]
    apply mul_nonneg _ hlow
    exact mul_nonneg (pow_nonneg (mul_nonneg hτ0.le
      (div_nonneg (sub_nonneg.mpr hb.1.le) (sub_pos.mpr hLv).le)) _)
      (div_nonneg hτ0.le (sub_pos.mpr hLv).le)

end RobustBidResearch

namespace RobustBidResearch

lemma maxLoss_compare (n : ℕ) (hn : 2 ≤ n) (τ L v b c : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hcomp : ∀ B ∈ varBidSet n τ L (uniformG L v), expUtil v b B ≤ expUtil v c B) :
    maxLoss v c (varBidSet n τ L (uniformG L v)) ≤
      maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  unfold maxLoss
  apply csSup_le
  · exact ⟨loss v c (commonBidEnv n τ (uniformG L v) L), _,
      common_admissible n hn τ L v hτ0 hτ1 hL hLv L le_rfl, rfl⟩
  · rintro _ ⟨B,hB,rfl⟩
    exact (sub_le_sub_left (hcomp B hB) _).trans
      (le_csSup (losses_bounded n τ L v b (hL.trans hLv.le) (uniformG L v)) ⟨B,hB,rfl⟩)

lemma peak_loss_lower (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbp : b < peakBid n τ L v) :
    uPlus n τ L v (peakBid n τ L v) - uMinus n τ L v (peakBid n τ L v) ≤
      maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  have hp := peak_bounds n hn τ L v hτ0 hLv
  have hm := minus_mono_before n hn τ L v hτ0 hτ1 hLv
  have hu := hm ⟨hLb,hbp.le⟩ ⟨hp.1,le_rfl⟩ hbp.le
  have hs : BddAbove (uPlus n τ L v '' Ioi b) := by
    refine ⟨v-L,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact uPlus_ray_bound n τ L v x hτ0.le hτ1.le hLv (hLb.trans hx.le)
  have he := le_csSup hs ⟨peakBid n τ L v,hbp,rfl⟩
  have hl := tooLow_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb (hbp.trans hp.2).le
  unfold tooLow at hl
  linarith

lemma equalizer_loss (n : ℕ) (hn : 2 ≤ n) (τ L v a : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (ha : peakBid n τ L v ≤ a ∧ a ≤ v ∧ Equation3 n τ L v a) :
    maxLoss v a (varBidSet n τ L (uniformG L v)) = uPlus n τ L v a-uMinus n τ L v a := by
  rw [maxLoss_formula n hn τ L v hτ0 hτ1 hL hLv a ((le_max_left _ _).trans ha.1) ha.2.1]
  have hh := formulas_after n hn τ L v a hτ0 hτ1 hLv ha.1
  rw [hh.1,hh.2,ha.2.2,max_self]

lemma equalizer_above_peak (n : ℕ) (hn : 2 ≤ n) (τ L v a : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v)
    (ha : peakBid n τ L v ≤ a ∧ a ≤ v ∧ Equation3 n τ L v a) :
    peakBid n τ L v < a := by
  by_contra h
  have he : a = peakBid n τ L v := le_antisymm (le_of_not_gt h) ha.1
  have hp := peak_bounds n hn τ L v hτ0 hLv
  have hg := gap_pos n hn τ L v (peakBid n τ L v) hτ0 hτ1 hLv hp.1 hp.2
  have hE := ha.2.2
  rw [he] at hE
  dsimp [Equation3] at hE
  linarith

lemma equalizer_strict_min (n : ℕ) (hn : 2 ≤ n) (τ L v a : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (ha : peakBid n τ L v ≤ a ∧ a ≤ v ∧ Equation3 n τ L v a) :
    ∀ b : ℝ, b ≠ a → maxLoss v a (varBidSet n τ L (uniformG L v)) <
      maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  have hp := peak_bounds n hn τ L v hτ0 hLv
  have hpa := equalizer_above_peak n hn τ L v a hτ0 hτ1 hLv ha
  have hla := equalizer_loss n hn τ L v a hτ0 hτ1 hL hLv ha
  have hga := gap_strict n hn τ L v hτ0 hτ1 hLv
  have hgap : uPlus n τ L v a-uMinus n τ L v a <
      uPlus n τ L v (peakBid n τ L v)-uMinus n τ L v (peakBid n τ L v) :=
    hga ⟨le_rfl,hp.2.le⟩ ⟨ha.1,ha.2.1⟩ hpa
  have hpeak : maxLoss v a (varBidSet n τ L (uniformG L v)) <
      maxLoss v (peakBid n τ L v) (varBidSet n τ L (uniformG L v)) := by
    have hl := tooLow_lower_bound n hn τ L v (peakBid n τ L v) hτ0 hτ1 hL hLv hp.1 hp.2.le
    rw [(formulas_after n hn τ L v (peakBid n τ L v) hτ0 hτ1 hLv le_rfl).2] at hl
    rw [hla]
    exact hgap.trans_le hl
  intro b hba
  by_cases hLb : L ≤ b
  · by_cases hbv : b ≤ v
    · by_cases hpb : peakBid n τ L v ≤ b
      · rcases lt_or_gt_of_ne hba with h | h
        · have hh := hga ⟨hpb,hbv⟩ ⟨ha.1,ha.2.1⟩ h
          have hl := tooLow_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb hbv
          rw [(formulas_after n hn τ L v b hτ0 hτ1 hLv hpb).2] at hl
          rw [hla]
          exact hh.trans_le hl
        · have hh := plus_strict_after n hn τ L v hτ0 hτ1 hLv
            ⟨ha.1,ha.2.1⟩ ⟨hpb,hbv⟩ h
          have hl := tooHigh_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb hbv
          rw [(formulas_after n hn τ L v b hτ0 hτ1 hLv hpb).1] at hl
          rw [hla]
          have he := ha.2.2
          dsimp [Equation3] at he
          linarith
      · rw [hla]
        exact hgap.trans_le (peak_loss_lower n hn τ L v b hτ0 hτ1 hL hLv hLb (lt_of_not_ge hpb))
    · apply hpeak.trans_le
      apply maxLoss_compare n hn τ L v b (peakBid n τ L v) hτ0 hτ1 hL hLv
      intro B hB
      exact (utility_above_value (n-1) v b (le_of_not_ge hbv) B).trans
        (utility_nonnegative (n-1) v (peakBid n τ L v) hp.2.le B)
  · apply hpeak.trans_le
    apply maxLoss_compare n hn τ L v b (peakBid n τ L v) hτ0 hτ1 hL hLv
    intro B hB
    rw [utility_below_floor n hn τ L v b (lt_of_not_ge hLb) (uniformG L v) B hB]
    exact utility_nonnegative (n-1) v (peakBid n τ L v) hp.2.le B

lemma minimax_characterization (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) :
    (∃! b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b) ∧
    (∀ b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b ↔
      (peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b)) ∧
    (∀ b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b →
      maxLoss v b (varBidSet n τ L (uniformG L v)) = uPlus n τ L v b-uMinus n τ L v b) := by
  obtain ⟨a,ha,huniq⟩ := (accepted_unique n hn τ L v hτ0 hτ1 hLv).2.2
  have hmin : IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) a := by
    refine ⟨hL.trans ((le_max_left _ _).trans ha.1),?_⟩
    intro b hb
    by_cases he : b=a
    · rw [he]
    · exact (equalizer_strict_min n hn τ L v a hτ0 hτ1 hL hLv ha b he).le
  have honly : ∀ b, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b → b=a := by
    intro b hb
    by_contra he
    exact (not_lt_of_ge (hb.2 a hmin.1))
      (equalizer_strict_min n hn τ L v a hτ0 hτ1 hL hLv ha b he)
  refine ⟨⟨a,hmin,honly⟩,?_,?_⟩
  · intro b
    constructor
    · intro hb; rw [honly b hb]; exact ha
    · intro hb; rw [huniq b hb]; exact hmin
  · intro b hb
    rw [honly b hb]
    exact equalizer_loss n hn τ L v a hτ0 hτ1 hL hLv ha

end RobustBidResearch

theorem solution (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) :
    (equalizerSet n τ L v).Nonempty ∧
    (∃ b, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b) ∧
    ∀ b, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b →
      b ∈ equalizerSet n τ L v ∧
      ∀ b' ∈ equalizerSet n τ L v, tooHigh n τ L v b ≤ tooHigh n τ L v b' := by
  have H := RobustBidResearch.minimax_characterization n hn τ L v hτ0 hτ1 hL hLv
  obtain ⟨a,ha,huniq⟩ := H.1
  have heq := equalizerSet_eq n hn τ L v hτ0 hτ1 hLv
  have hai : a ∈ equalizerSet n τ L v := by rw [heq]; exact (H.2.1 a).mp ha
  refine ⟨⟨a,hai⟩,⟨a,ha⟩,?_⟩
  intro b hb
  have hbi : b ∈ equalizerSet n τ L v := by rw [heq]; exact (H.2.1 b).mp hb
  refine ⟨hbi,?_⟩
  intro c hc
  have hcm : IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) c := by
    apply (H.2.1 c).mpr
    rw [heq] at hc
    exact hc
  rw [huniq b hb,huniq c hcm]
#print axioms solution


end AcceptedMinimax

/- Full Proposition 4. This includes the complete accepted Proposition3 body,
submission 0d86a5ff-29de-49a9-a57a-b01fe784fe09, SHA256
f7b7b946c1668f86fc28689b95b95319cb79ae0d6e745fbdd4f46142844d9f09,
and the complete new consecutive-bidder comparison. Earlier work and all inherited
source/platform/library attribution remain credited. The new increment closes
strict bidder-count comparative statics and assembles the full exact root. -/
open RobustFPA.VarBid

theorem solution (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) :
    (∃! b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b) ∧
    (∀ b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b ↔
      (peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b)) ∧
    (∀ b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b →
      maxLoss v b (varBidSet n τ L (uniformG L v)) = uPlus n τ L v b - uMinus n τ L v b) ∧
    (∀ b b' : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b →
      IsMinimaxLossBid v (varBidSet (n + 1) τ L (uniformG L v)) b' → b < b') := by
  have H := AcceptedMinimax.RobustBidResearch.minimax_characterization n hn τ L v hτ0 hτ1 hL hLv
  refine ⟨H.1,H.2.1,H.2.2,?_⟩
  intro b b' hb hb'
  have hn' : 2 ≤ n+1 := by omega
  have H' := AcceptedMinimax.RobustBidResearch.minimax_characterization (n+1) hn' τ L v hτ0 hτ1 hL hLv
  exact ComparisonSource.solution n hn τ L v hτ0 hτ1 hLv b b' ((H.2.1 b).mp hb) ((H'.2.1 b').mp hb')

#print axioms solution
