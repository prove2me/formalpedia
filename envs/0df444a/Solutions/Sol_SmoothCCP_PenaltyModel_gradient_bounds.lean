-- Prove2me | solution 1 for SmoothCCP.PenaltyModel.gradient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:32:45.511078+00:00
-- url     : https://prove2.me/submissions/1f92e081-dbb9-4587-ba77-3491db088520

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace SCQK

noncomputable def P (u : ℝ) : ℝ := 15 / 16 * (-(1 / 5) * u ^ 5 + 2 / 3 * u ^ 3 - u + 8 / 15)
noncomputable def P' (u : ℝ) : ℝ := -(15 / 16) * (1 - u ^ 2) ^ 2
noncomputable def cl (u : ℝ) : ℝ := min (max u (-1)) 1
noncomputable def G (u : ℝ) : ℝ := P (cl u)

lemma hasDerivAt_P (u : ℝ) : HasDerivAt P (P' u) u := by
  have h := ((((hasDerivAt_pow 5 u).const_mul (-(1/5:ℝ))).add
    ((hasDerivAt_pow 3 u).const_mul (2/3:ℝ))).sub (hasDerivAt_id u)).add_const (8/15:ℝ)
  have h2 := h.const_mul (15/16:ℝ)
  exact h2.congr_deriv (by simp only [P']; push_cast; ring)

lemma hasDerivAt_comp_min {f f' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y) (a : ℝ)
    (ha : f' a = 0) (u : ℝ) : HasDerivAt (fun v => f (min v a)) (f' (min u a)) u := by
  rcases lt_trichotomy u a with h | h | h
  · rw [min_eq_left h.le]
    apply (hf u).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with v hv
    simp [min_eq_left (Set.mem_Iio.mp hv).le]
  · subst h
    simp only [min_self, ha]
    have h1 : HasDerivWithinAt (fun v => f (min v u)) 0 (Set.Iic u) u := by
      have := (hf u).hasDerivWithinAt (s := Set.Iic u)
      rw [ha] at this
      apply this.congr
      · intro v hv; simp [min_eq_left (show v ≤ u from hv)]
      · simp
    have h2 : HasDerivWithinAt (fun v => f (min v u)) 0 (Set.Ici u) u := by
      have := (hasDerivWithinAt_const u (Set.Ici u) (f u))
      apply this.congr
      · intro v hv; simp [min_eq_right (show u ≤ v from hv)]
      · simp
    have := h1.union h2
    rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this
  · rw [min_eq_right h.le, ha]
    apply (hasDerivAt_const u (f a)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with v hv
    simp [min_eq_right (Set.mem_Ioi.mp hv).le]

lemma hasDerivAt_comp_max {f f' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y) (a : ℝ)
    (ha : f' a = 0) (u : ℝ) : HasDerivAt (fun v => f (max v a)) (f' (max u a)) u := by
  have hf2 : ∀ y, HasDerivAt (fun v => f (-v)) (-f' (-y)) y := fun y => by
    exact ((hf (-y)).comp y (hasDerivAt_neg y)).congr_deriv (by ring)
  have key := hasDerivAt_comp_min hf2 (-a) (by simp [ha]) (-u)
  have := key.comp u (hasDerivAt_neg u)
  have e : (fun v => f (max v a)) = (fun v => f (-min v (-a))) ∘ Neg.neg := by
    funext v; simp [min_neg_neg]
  rw [e]
  exact this.congr_deriv (by simp [min_neg_neg])

lemma hasDerivAt_G (u : ℝ) : HasDerivAt G (P' (cl u)) u := by
  have hB : ∀ y, HasDerivAt (fun v => P (min v 1)) (P' (min y 1)) y :=
    hasDerivAt_comp_min hasDerivAt_P 1 (by norm_num [P'])
  exact hasDerivAt_comp_max hB (-1) (by norm_num [P']) u

lemma cl_le (u : ℝ) : cl u ≤ 1 := min_le_right _ _
lemma le_cl (u : ℝ) : -1 ≤ cl u := le_min (le_max_right _ _) (by norm_num)
lemma cl_lip (a b : ℝ) : |cl a - cl b| ≤ |a - b| := by
  unfold cl
  calc |min (max a (-1)) 1 - min (max b (-1)) 1| ≤ |max a (-1) - max b (-1)| := by
        have := abs_min_sub_min_le_max (max a (-1)) 1 (max b (-1)) 1
        simpa using this
    _ ≤ |a - b| := abs_max_sub_max_le_abs _ _ _

lemma w_lip {a b : ℝ} (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hb1 : -1 ≤ b) (hb2 : b ≤ 1) :
    |(1 - a ^ 2) ^ 2 - (1 - b ^ 2) ^ 2| ≤ 4 * |a - b| := by
  have e : (1 - a ^ 2) ^ 2 - (1 - b ^ 2) ^ 2 = (a - b) * ((a + b) * (a ^ 2 + b ^ 2 - 2)) := by ring
  rw [e, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [abs_mul]
  have h1 : |a + b| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h2 : |a ^ 2 + b ^ 2 - 2| ≤ 2 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  calc |a + b| * |a ^ 2 + b ^ 2 - 2| ≤ 2 * 2 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 4 := by norm_num

lemma P'cl_lip (a b : ℝ) : |P' (cl a) - P' (cl b)| ≤ 15 / 4 * |a - b| := by
  have e : P' (cl a) - P' (cl b) = -(15/16) * ((1 - cl a ^ 2) ^ 2 - (1 - cl b ^ 2) ^ 2) := by
    simp only [P']; ring
  rw [e, abs_mul]
  have := w_lip (le_cl a) (cl_le a) (le_cl b) (cl_le b)
  have := cl_lip a b
  norm_num; nlinarith [abs_nonneg (a - b)]

lemma G_taylor (u v : ℝ) : |G v - G u - P' (cl u) * (v - u)| ≤ 15 / 4 * (v - u) ^ 2 := by
  have hd : ∀ s ∈ Set.uIcc u v, HasDerivWithinAt (fun s => G s - P' (cl u) * s)
      (P' (cl s) - P' (cl u)) (Set.uIcc u v) s := by
    intro s _
    have := ((hasDerivAt_G s).sub ((hasDerivAt_id s).const_mul (P' (cl u))))
    exact this.hasDerivWithinAt.congr_deriv (by ring)
  have hb : ∀ s ∈ Set.uIcc u v, ‖P' (cl s) - P' (cl u)‖ ≤ 15 / 4 * |v - u| := by
    intro s hs
    rw [Real.norm_eq_abs]
    refine (P'cl_lip s u).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [Set.mem_uIcc] at hs
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have := (convex_uIcc u v).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs] at this
  have e : G v - P' (cl u) * v - (G u - P' (cl u) * u) = G v - G u - P' (cl u) * (v - u) := by ring
  rw [e] at this
  calc _ ≤ 15 / 4 * |v - u| * |v - u| := this
    _ = 15 / 4 * (v - u) ^ 2 := by rw [mul_assoc, ← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]

lemma G_diff : Differentiable ℝ G := fun u => (hasDerivAt_G u).differentiableAt

lemma G_anti : Antitone G := by
  apply antitone_of_deriv_nonpos G_diff
  intro u; rw [(hasDerivAt_G u).deriv]; simp only [P']; nlinarith [sq_nonneg (1 - cl u ^ 2)]

lemma G_cont : Continuous G := G_diff.continuous

lemma G_of_le {u : ℝ} (h : u ≤ -1) : G u = 1 := by
  simp only [G, cl, max_eq_right h]; norm_num [P]

lemma G_of_ge {u : ℝ} (h : 1 ≤ u) : G u = 0 := by
  simp only [G, cl, max_eq_left (show (-1:ℝ) ≤ u by linarith), min_eq_right h]; norm_num [P]

lemma P_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ P t ∧ P t ≤ (1 - t ^ 2) ^ 2 := by
  have e1 : P t = (1 - t) ^ 3 * (3 * t ^ 2 + 9 * t + 8) / 16 := by simp only [P]; ring
  have e2 : (1 - t ^ 2) ^ 2 - P t = (t - 1) ^ 2 * (3 * t + 1) * (t ^ 2 + 7 * t + 8) / 16 := by
    simp only [P]; ring
  constructor
  · rw [e1]; have : 0 ≤ (1 - t) ^ 3 := pow_nonneg (by linarith) 3
    positivity
  · have : 0 ≤ (t - 1) ^ 2 * (3 * t + 1) * (t ^ 2 + 7 * t + 8) / 16 := by
      have : 0 ≤ 3 * t + 1 := by linarith
      positivity
    linarith

lemma G_near_int (u : ℝ) : ∃ k : ℤ, |G u - k| ≤ (1 - cl u ^ 2) ^ 2 := by
  rcases le_total (cl u) 0 with h | h
  · refine ⟨1, ?_⟩
    have hs : P (cl u) = 1 - P (-cl u) := by simp only [P]; ring
    obtain ⟨a, b⟩ := P_bounds (t := -cl u) (by linarith) (by linarith [le_cl u])
    simp only [G, Int.cast_one]
    rw [hs, abs_le]; constructor <;> nlinarith
  · refine ⟨0, ?_⟩
    obtain ⟨a, b⟩ := P_bounds (t := cl u) h (cl_le u)
    simp only [G, Int.cast_zero, sub_zero]
    rw [abs_le]; constructor <;> nlinarith

lemma gam_eq (ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    SmoothCCP.Feasibility.Gam ε (SmoothCCP.PenaltyModel.quarticGamma ε) y = G (y / ε) := by
  unfold SmoothCCP.Feasibility.Gam
  split_ifs with h1 h2
  · rw [G_of_le]; rw [div_le_iff₀ hε]; linarith
  · have a : -1 < y / ε := by rw [lt_div_iff₀ hε]; linarith
    have b : y / ε < 1 := by rw [div_lt_iff₀ hε]; linarith
    simp only [G, cl, max_eq_left a.le, min_eq_left b.le, P, SmoothCCP.PenaltyModel.quarticGamma]
  · rw [G_of_ge]; rw [le_div_iff₀ hε]; linarith

lemma gam_fun_eq (ε : ℝ) (hε : 0 < ε) :
    SmoothCCP.Feasibility.Gam ε (SmoothCCP.PenaltyModel.quarticGamma ε) = fun y => G (y / ε) :=
  funext (gam_eq ε hε)

lemma hasDerivAt_gam (ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (SmoothCCP.Feasibility.Gam ε (SmoothCCP.PenaltyModel.quarticGamma ε))
      (P' (cl (y / ε)) / ε) y := by
  rw [gam_fun_eq ε hε]
  have := (hasDerivAt_G (y / ε)).comp y ((hasDerivAt_id' y).div_const ε)
  exact this.congr_deriv (by rw [mul_one_div])

end SCQK

namespace SCQK

variable {N : ℕ}

noncomputable def hs (ε : ℝ) (z : Fin N → ℝ) (q : ℝ) : ℝ := ∑ i, G ((z i - q) / ε)

noncomputable def Qf (ε α : ℝ) (z : Fin N → ℝ) : ℝ :=
  sInf {q : ℝ | (1 - α) * N ≤ hs ε z q}

lemma sq_eq (ε α : ℝ) (hε : 0 < ε) :
    SmoothCCP.PenaltyModel.smoothQuantile (N := N) ε (SmoothCCP.PenaltyModel.quarticGamma ε) α
      = Qf ε α := by
  funext z
  unfold SmoothCCP.PenaltyModel.smoothQuantile Qf hs
  rw [gam_fun_eq ε hε]

section
variable {ε α : ℝ} (hε : 0 < ε) (hT0 : 0 < (1 - α) * N) (hT1 : (1 - α) * N < N)
include hε

lemma hs_mono (z : Fin N → ℝ) {q q' : ℝ} (h : q ≤ q') : hs ε z q ≤ hs ε z q' := by
  apply Finset.sum_le_sum; intro i _
  apply G_anti
  exact div_le_div_of_nonneg_right (by linarith) hε.le

omit hε in
lemma hs_cont (z : Fin N → ℝ) : Continuous (hs ε z) := by
  unfold hs
  have := G_cont
  fun_prop

lemma hs_low (z : Fin N → ℝ) {q : ℝ} (h : q ≤ -‖z‖ - ε) : hs ε z q = 0 := by
  unfold hs
  apply Finset.sum_eq_zero; intro i _
  apply G_of_ge
  rw [le_div_iff₀ hε]
  have := (abs_le.mp ((Real.norm_eq_abs (z i)).symm ▸ norm_le_pi_norm z i)).1
  linarith

lemma hs_high (z : Fin N → ℝ) {q : ℝ} (h : ‖z‖ + ε ≤ q) : hs ε z q = N := by
  unfold hs
  rw [Finset.sum_eq_card_nsmul (b := 1)]
  · simp
  intro i _
  apply G_of_le
  rw [div_le_iff₀ hε]
  have := (abs_le.mp ((Real.norm_eq_abs (z i)).symm ▸ norm_le_pi_norm z i)).2
  linarith

include hT0 in
lemma S_bdd (z : Fin N → ℝ) : BddBelow {q : ℝ | (1 - α) * N ≤ hs ε z q} := by
  refine ⟨-‖z‖ - ε, fun q hq => ?_⟩
  by_contra hc
  push_neg at hc
  have := hs_low hε z hc.le
  simp only [Set.mem_setOf_eq] at hq
  linarith

include hT1 in
lemma S_ne (z : Fin N → ℝ) : (‖z‖ + ε) ∈ {q : ℝ | (1 - α) * N ≤ hs ε z q} := by
  simp only [Set.mem_setOf_eq]; rw [hs_high hε z le_rfl]; linarith

include hT0 hT1 in
lemma Q_mem (z : Fin N → ℝ) : (1 - α) * N ≤ hs ε z (Qf ε α z) := by
  have hc : IsClosed {q : ℝ | (1 - α) * N ≤ hs ε z q} := isClosed_le continuous_const (hs_cont z)
  exact hc.csInf_mem ⟨_, S_ne hε hT1 z⟩ (S_bdd hε hT0 z)

include hT0 hT1 in
lemma Q_eq (z : Fin N → ℝ) : hs ε z (Qf ε α z) = (1 - α) * N := by
  apply le_antisymm _ (Q_mem hε hT0 hT1 z)
  by_contra hc
  push_neg at hc
  have hev : ∀ᶠ q in nhds (Qf ε α z), (1 - α) * N < hs ε z q :=
    ((hs_cont z).tendsto _).eventually (lt_mem_nhds hc)
  obtain ⟨q, hq1, hq2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Iio (Qf ε α z)))).exists
  have : Qf ε α z ≤ q := csInf_le (S_bdd hε hT0 z) (show (1 - α) * N ≤ hs ε z q from hq1.le)
  exact absurd hq2 (not_lt.mpr this)

include hT0 hT1 in
lemma Q_le (z z' : Fin N → ℝ) : Qf ε α z' ≤ Qf ε α z + ‖z' - z‖ := by
  apply csInf_le (S_bdd hε hT0 z')
  simp only [Set.mem_setOf_eq]
  refine (Q_mem hε hT0 hT1 z).trans ?_
  apply Finset.sum_le_sum; intro i _
  apply G_anti
  apply div_le_div_of_nonneg_right _ hε.le
  have := (abs_le.mp ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm (z' - z) i)).2
  simp only [Pi.sub_apply] at this
  linarith

include hT0 hT1 in
lemma Q_lip (z z' : Fin N → ℝ) : |Qf ε α z' - Qf ε α z| ≤ ‖z' - z‖ := by
  have a := Q_le hε hT0 hT1 z z'
  have b := Q_le hε hT0 hT1 z' z
  rw [norm_sub_rev] at b
  rw [abs_le]; constructor <;> linarith

end

noncomputable def wt (ε α : ℝ) (z : Fin N → ℝ) (i : Fin N) : ℝ :=
  (1 - cl ((z i - Qf ε α z) / ε) ^ 2) ^ 2

noncomputable def Wt (ε α : ℝ) (z : Fin N → ℝ) : ℝ := ∑ i, wt ε α z i

lemma wt_nonneg (ε α : ℝ) (z : Fin N → ℝ) (i : Fin N) : 0 ≤ wt ε α z i := sq_nonneg _

lemma wt_le_one (ε α : ℝ) (z : Fin N → ℝ) (i : Fin N) : wt ε α z i ≤ 1 := by
  unfold wt
  have h1 := le_cl ((z i - Qf ε α z) / ε)
  have h2 := cl_le ((z i - Qf ε α z) / ε)
  have : 0 ≤ 1 - cl ((z i - Qf ε α z) / ε) ^ 2 := by nlinarith
  have : 1 - cl ((z i - Qf ε α z) / ε) ^ 2 ≤ 1 := by nlinarith
  nlinarith

lemma Wt_le (ε α : ℝ) (z : Fin N → ℝ) : Wt ε α z ≤ N := by
  unfold Wt
  calc ∑ i, wt ε α z i ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => wt_le_one ε α z i)
    _ = N := by simp

lemma int_gap {T : ℝ} (hT : ∀ k : ℤ, T ≠ k) (k : ℤ) :
    min (Int.fract T) (1 - Int.fract T) ≤ |T - k| := by
  have hf : Int.fract T = T - ⌊T⌋ := rfl
  rcases le_or_gt k ⌊T⌋ with h | h
  · have : (k:ℝ) ≤ ⌊T⌋ := by exact_mod_cast h
    have h0 : (⌊T⌋ : ℝ) ≤ T := Int.floor_le T
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have : (⌊T⌋ : ℝ) + 1 ≤ k := by exact_mod_cast h
    have h0 : T < (⌊T⌋ : ℝ) + 1 := Int.lt_floor_add_one T
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

lemma gap_pos {T : ℝ} (hT : ∀ k : ℤ, T ≠ k) : 0 < min (Int.fract T) (1 - Int.fract T) := by
  apply lt_min
  · rw [Int.fract_pos]; exact hT _
  · linarith [Int.fract_lt_one T]

lemma Wt_lb {ε α : ℝ} (hε : 0 < ε) (hT0 : 0 < (1 - α) * N) (hT1 : (1 - α) * N < N)
    (hαN : ∀ k : ℤ, (1 - α) * N ≠ k) (z : Fin N → ℝ) :
    min (Int.fract ((1 - α) * N)) (1 - Int.fract ((1 - α) * N)) ≤ Wt ε α z := by
  have hk : ∀ i : Fin N, ∃ k : ℤ, |G ((z i - Qf ε α z) / ε) - k| ≤ wt ε α z i :=
    fun i => G_near_int _
  choose k hk using hk
  have := int_gap hαN (∑ i, k i)
  refine this.trans ?_
  rw [← Q_eq hε hT0 hT1 z]
  unfold hs Wt
  push_cast
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hk i)

end SCQK

namespace SCQK

variable {N : ℕ}

noncomputable def Dq (ε α : ℝ) (z : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ i, (wt ε α z i / Wt ε α z) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i

lemma Dq_apply (ε α : ℝ) (z p : Fin N → ℝ) :
    Dq ε α z p = (∑ i, wt ε α z i * p i) / Wt ε α z := by
  simp only [Dq, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_proj, smul_eq_mul, Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _; rw [ContinuousLinearMap.proj_apply]; ring

lemma abs_coord_le (p : Fin N → ℝ) (i : Fin N) : |p i| ≤ ‖p‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm p i

section
variable {ε α : ℝ} (hε : 0 < ε) (hT0 : 0 < (1 - α) * N) (hT1 : (1 - α) * N < N)
  (hαN : ∀ k : ℤ, (1 - α) * N ≠ k)
include hε hT0 hT1 hαN

lemma Q_taylor (z p : Fin N → ℝ) :
    |Qf ε α (z + p) - Qf ε α z - (∑ i, wt ε α z i * p i) / Wt ε α z|
      ≤ 16 * N / (ε * min (Int.fract ((1 - α) * N)) (1 - Int.fract ((1 - α) * N))) * ‖p‖ ^ 2 := by
  set κ := min (Int.fract ((1 - α) * N)) (1 - Int.fract ((1 - α) * N)) with hκdef
  have hκ : 0 < κ := gap_pos hαN
  have hW : κ ≤ Wt ε α z := Wt_lb hε hT0 hT1 hαN z
  have hWpos : 0 < Wt ε α z := lt_of_lt_of_le hκ hW
  set δ := Qf ε α (z + p) - Qf ε α z with hδ
  set A := ∑ i, wt ε α z i * p i with hA
  set W := Wt ε α z with hWdef
  have hδb : |δ| ≤ ‖p‖ := by
    have := Q_lip hε hT0 hT1 z (z + p); simpa using this
  set u : Fin N → ℝ := fun i => (z i - Qf ε α z) / ε with hu
  set v : Fin N → ℝ := fun i => ((z + p) i - Qf ε α (z + p)) / ε with hv
  have hvu : ∀ i, v i - u i = (p i - δ) / ε := by
    intro i; simp only [hu, hv, hδ, Pi.add_apply]; field_simp; ring
  have hvub : ∀ i, (v i - u i) ^ 2 ≤ (2 * ‖p‖ / ε) ^ 2 := by
    intro i
    rw [hvu i, div_pow, div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have a := abs_le.mp (abs_coord_le p i)
    have b := abs_le.mp hδb
    apply sq_le_sq'
    · linarith [a.1, a.2, b.1, b.2]
    · linarith [a.1, a.2, b.1, b.2]
  set r : Fin N → ℝ := fun i => G (v i) - G (u i) - P' (cl (u i)) * (v i - u i) with hr
  have hrb : ∀ i, |r i| ≤ 15 / 4 * (2 * ‖p‖ / ε) ^ 2 := fun i =>
    (G_taylor (u i) (v i)).trans (by nlinarith [hvub i])
  have hsum : ∑ i, G (v i) = ∑ i, G (u i) := by
    have a := Q_eq hε hT0 hT1 z
    have b := Q_eq hε hT0 hT1 (z + p)
    unfold hs at a b
    exact b.trans a.symm
  have hR : ∑ i, r i = 15 / (16 * ε) * (A - δ * W) := by
    have e1 : ∀ i, r i = (G (v i) - G (u i)) + 15 / (16 * ε) * (wt ε α z i * p i - δ * wt ε α z i) := by
      intro i
      simp only [hr]
      rw [hvu i]
      simp only [P', wt, hu]
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hsum, sub_self, zero_add, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  have hRb : |∑ i, r i| ≤ N * (15 / 4 * (2 * ‖p‖ / ε) ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |r i| ≤ ∑ _i : Fin N, 15 / 4 * (2 * ‖p‖ / ε) ^ 2 := Finset.sum_le_sum fun i _ => hrb i
      _ = _ := by simp
  have key : |δ * W - A| = 16 * ε / 15 * |∑ i, r i| := by
    rw [hR, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 15 / (16 * ε)), abs_sub_comm]
    field_simp
  have e2 : δ - A / W = (δ * W - A) / W := by field_simp
  rw [e2, abs_div, abs_of_pos hWpos, div_le_iff₀ hWpos, key]
  have : 16 * ε / 15 * |∑ i, r i| ≤ 16 * ε / 15 * (N * (15 / 4 * (2 * ‖p‖ / ε) ^ 2)) :=
    mul_le_mul_of_nonneg_left hRb (by positivity)
  refine this.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hW (by positivity)))
  field_simp
  ring

lemma Q_hasFDerivAt (z : Fin N → ℝ) : HasFDerivAt (Qf ε α) (Dq ε α z) z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun p => Qf ε α (z + p) - Qf ε α z - Dq ε α z p) =O[nhds 0] (fun p : Fin N → ℝ => ‖p‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound
      (16 * N / (ε * min (Int.fract ((1 - α) * N)) (1 - Int.fract ((1 - α) * N))))
    filter_upwards with p
    rw [Dq_apply, Real.norm_eq_abs, norm_pow, norm_norm]
    exact Q_taylor hε hT0 hT1 hαN z p
  exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

end

lemma opnorm_sum_proj_le (c : Fin N → ℝ) :
    ‖∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i‖ ≤ ∑ i, |c i| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
  intro p
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_proj, smul_eq_mul, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_coord_le p i) (abs_nonneg _)

section
variable {ε α : ℝ} (hε : 0 < ε) (hT0 : 0 < (1 - α) * N) (hT1 : (1 - α) * N < N)
  (hαN : ∀ k : ℤ, (1 - α) * N ≠ k)
include hε hT0 hT1 hαN

lemma Dq_norm_le (z : Fin N → ℝ) : ‖Dq ε α z‖ ≤ 1 := by
  have hWpos : 0 < Wt ε α z := lt_of_lt_of_le (gap_pos hαN) (Wt_lb hε hT0 hT1 hαN z)
  refine (opnorm_sum_proj_le _).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun i _ => abs_of_nonneg (div_nonneg (wt_nonneg ε α z i) hWpos.le)),
    ← Finset.sum_div]
  exact div_self hWpos.ne'

omit hαN in
lemma wt_lip (z z' : Fin N → ℝ) (i : Fin N) :
    |wt ε α z i - wt ε α z' i| ≤ 8 / ε * ‖z - z'‖ := by
  unfold wt
  refine (w_lip (le_cl _) (cl_le _) (le_cl _) (cl_le _)).trans ?_
  have h1 := cl_lip ((z i - Qf ε α z) / ε) ((z' i - Qf ε α z') / ε)
  have h2 : |(z i - Qf ε α z) / ε - (z' i - Qf ε α z') / ε| ≤ 2 * ‖z - z'‖ / ε := by
    rw [← sub_div, abs_div, abs_of_pos hε]
    apply div_le_div_of_nonneg_right _ hε.le
    have a := abs_coord_le (z - z') i
    have b := Q_lip hε hT0 hT1 z' z
    simp only [Pi.sub_apply] at a
    calc |z i - Qf ε α z - (z' i - Qf ε α z')| = |(z i - z' i) - (Qf ε α z - Qf ε α z')| := by ring_nf
      _ ≤ |z i - z' i| + |Qf ε α z - Qf ε α z'| := abs_sub _ _
      _ ≤ _ := by linarith
  have : 4 * (2 * ‖z - z'‖ / ε) = 8 / ε * ‖z - z'‖ := by ring
  linarith

lemma ratio_lip (z z' : Fin N → ℝ) (i : Fin N) :
    |wt ε α z i / Wt ε α z - wt ε α z' i / Wt ε α z'|
      ≤ 16 * N / (ε * (min (Int.fract ((1 - α) * N)) (1 - Int.fract ((1 - α) * N))) ^ 2)
          * ‖z - z'‖ := by
  set κ := min (Int.fract ((1 - α) * N)) (1 - Int.fract ((1 - α) * N))
  have hκ : 0 < κ := gap_pos hαN
  have hW : κ ≤ Wt ε α z := Wt_lb hε hT0 hT1 hαN z
  have hW' : κ ≤ Wt ε α z' := Wt_lb hε hT0 hT1 hαN z'
  have hWp : 0 < Wt ε α z := lt_of_lt_of_le hκ hW
  have hWp' : 0 < Wt ε α z' := lt_of_lt_of_le hκ hW'
  set W := Wt ε α z
  set W' := Wt ε α z'
  set w := wt ε α z i
  set w' := wt ε α z' i
  have hww := wt_lip hε hT0 hT1 z z' i
  have hWW : |W - W'| ≤ N * (8 / ε * ‖z - z'‖) := by
    simp only [W, W', Wt]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |wt ε α z j - wt ε α z' j| ≤ ∑ _j : Fin N, 8 / ε * ‖z - z'‖ :=
          Finset.sum_le_sum fun j _ => wt_lip hε hT0 hT1 z z' j
      _ = _ := by simp
  have hw'1 : w' ≤ 1 := wt_le_one ε α z' i
  have hw'0 : 0 ≤ w' := wt_nonneg ε α z' i
  have hW'N : W' ≤ N := Wt_le ε α z'
  have e : w / W - w' / W' = ((w - w') * W' + w' * (W' - W)) / (W * W') := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos hWp hWp'), div_le_iff₀ (mul_pos hWp hWp')]
  have hnum : |(w - w') * W' + w' * (W' - W)| ≤ 16 * N / ε * ‖z - z'‖ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hWp', abs_of_nonneg hw'0, abs_sub_comm W' W]
    have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
    have : 0 ≤ 8 / ε * ‖z - z'‖ := by positivity
    have a : |w - w'| * W' ≤ (8 / ε * ‖z - z'‖) * N :=
      mul_le_mul hww hW'N hWp'.le this
    have b : w' * |W - W'| ≤ 1 * (N * (8 / ε * ‖z - z'‖)) :=
      mul_le_mul hw'1 hWW (abs_nonneg _) (by norm_num)
    have : 16 * N / ε * ‖z - z'‖ = (8 / ε * ‖z - z'‖) * N + 1 * (N * (8 / ε * ‖z - z'‖)) := by ring
    linarith
  refine hnum.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left
    (mul_le_mul hW hW' hκ.le hWp.le) (by positivity)))
  field_simp

lemma Dq_lip (z z' : Fin N → ℝ) :
    ‖Dq ε α z - Dq ε α z'‖ ≤ N * (16 * N / (ε * (min (Int.fract ((1 - α) * N))
      (1 - Int.fract ((1 - α) * N))) ^ 2)) * ‖z - z'‖ := by
  have e : Dq ε α z - Dq ε α z' = ∑ i, (wt ε α z i / Wt ε α z - wt ε α z' i / Wt ε α z') •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i := by
    simp only [Dq, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
  rw [e]
  refine (opnorm_sum_proj_le _).trans ?_
  calc ∑ i, |wt ε α z i / Wt ε α z - wt ε α z' i / Wt ε α z'|
      ≤ ∑ _i : Fin N, 16 * N / (ε * (min (Int.fract ((1 - α) * N))
          (1 - Int.fract ((1 - α) * N))) ^ 2) * ‖z - z'‖ :=
        Finset.sum_le_sum fun i _ => ratio_lip hε hT0 hT1 hαN z z' i
    _ = _ := by simp; ring

end

end SCQK

namespace SCQK

lemma T_bounds {N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hN : 1 ≤ N) :
    0 < (1 - α) * N ∧ (1 - α) * N < N := by
  have : (1:ℝ) ≤ N := by exact_mod_cast hN
  constructor <;> nlinarith

lemma deriv_gam_eq {N : ℕ} {ε α : ℝ} (hε : 0 < ε) (z : Fin N → ℝ) (i : Fin N) :
    deriv (SmoothCCP.Feasibility.Gam ε (SmoothCCP.PenaltyModel.quarticGamma ε)) (z i - Qf ε α z)
      = -(15 / (16 * ε)) * wt ε α z i := by
  rw [(hasDerivAt_gam ε hε _).deriv]
  simp only [P', wt]; field_simp

lemma sum_deriv_gam_eq {N : ℕ} {ε α : ℝ} (hε : 0 < ε) (z : Fin N → ℝ) :
    ∑ j, deriv (SmoothCCP.Feasibility.Gam ε (SmoothCCP.PenaltyModel.quarticGamma ε)) (z j - Qf ε α z)
      = -(15 / (16 * ε)) * Wt ε α z := by
  simp only [deriv_gam_eq hε, Wt, Finset.mul_sum]

end SCQK

open SmoothCCP.PenaltyModel in
theorem solution {N : ℕ} (ε α : ℝ) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1)
    (hN : 1 ≤ N) (hαN : ∀ k : ℤ, (1 - α) * N ≠ k) :
    (∃ κ : ℝ, 0 < κ ∧ ∀ z : Fin N → ℝ,
        ∑ j : Fin N, deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z j - smoothQuantile ε (quarticGamma ε) α z)
          ≤ -κ) ∧
      ∀ (z : Fin N → ℝ) (i : Fin N),
        0 ≤ deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z i - smoothQuantile ε (quarticGamma ε) α z) /
            ∑ j : Fin N, deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z j - smoothQuantile ε (quarticGamma ε) α z) ∧
        deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z i - smoothQuantile ε (quarticGamma ε) α z) /
            ∑ j : Fin N, deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z j - smoothQuantile ε (quarticGamma ε) α z)
          ≤ 1 := by
  obtain ⟨hT0, hT1⟩ := SCQK.T_bounds (N := N) hα0 hα1 hN
  rw [SCQK.sq_eq ε α hε]
  have hκ := SCQK.gap_pos hαN
  refine ⟨⟨15 / (16 * ε) * min (Int.fract ((1 - α) * N)) (1 - Int.fract ((1 - α) * N)),
    by positivity, fun z => ?_⟩, fun z i => ?_⟩
  · rw [SCQK.sum_deriv_gam_eq hε]
    have := SCQK.Wt_lb hε hT0 hT1 hαN z
    have : 0 < 15 / (16 * ε) := by positivity
    nlinarith
  · have hWp : 0 < SCQK.Wt ε α z := lt_of_lt_of_le hκ (SCQK.Wt_lb hε hT0 hT1 hαN z)
    rw [SCQK.sum_deriv_gam_eq hε, SCQK.deriv_gam_eq hε]
    have hc : (0:ℝ) < 15 / (16 * ε) := by positivity
    have e : -(15 / (16 * ε)) * SCQK.wt ε α z i / (-(15 / (16 * ε)) * SCQK.Wt ε α z)
        = SCQK.wt ε α z i / SCQK.Wt ε α z := by
      rw [mul_div_mul_left _ _ (neg_ne_zero.mpr hc.ne')]
    rw [e]
    refine ⟨div_nonneg (SCQK.wt_nonneg ε α z i) hWp.le, (div_le_one hWp).mpr ?_⟩
    exact Finset.single_le_sum (f := SCQK.wt ε α z) (fun j _ => SCQK.wt_nonneg ε α z j)
      (Finset.mem_univ i)
