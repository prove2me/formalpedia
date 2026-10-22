-- Prove2me | solution 1 for RobustFPA.VarBid.equalizerSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T17:37:07.009527+00:00
-- url     : https://prove2.me/submissions/a451dfdb-e5d9-46c6-a666-5518064e9596

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
