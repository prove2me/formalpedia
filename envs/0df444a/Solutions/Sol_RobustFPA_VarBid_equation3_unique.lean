-- Prove2me | solution 1 for RobustFPA.VarBid.equation3_unique
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T16:24:42.002565+00:00
-- url     : https://prove2.me/submissions/f545c89e-c78c-4d50-8cf4-aab933f74ba3

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
theorem solution (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
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
#print axioms solution
