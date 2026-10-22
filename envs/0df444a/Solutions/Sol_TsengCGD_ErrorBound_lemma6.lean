-- Prove2me | solution 1 for TsengCGD.ErrorBound.lemma6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:40:30.082991+00:00
-- url     : https://prove2.me/submissions/fa9e3856-62ca-4cb2-86b6-e623cffd1b0d

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
import Definitions.Def_TsengCGD_ErrorBound_Conditions

open scoped RealInnerProductSpace

namespace TsengCGD.ErrorBound

lemma l6_sq_path {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) (s : ℝ) :
    ‖a + s • (b - a)‖^2 = (1-s)*‖a‖^2 + s*‖b‖^2 - s*(1-s)*‖b-a‖^2 := by
  have h1 : ‖a + s • (b - a)‖^2 = ‖a‖^2 + 2 * s * ⟪a, b - a⟫ + s^2 * ‖b-a‖^2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  have h2 : ‖b‖^2 = ‖a + (b - a)‖^2 := by simp
  rw [norm_add_sq_real] at h2
  rw [h1, h2]; ring

lemma l6_quad {A B N : ℝ} (hN : 0 ≤ N)
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → A ≤ (1-s)*A + s*B - s*(1-s)/2*N) : A + N/2 ≤ B := by
  by_contra hlt
  push_neg at hlt
  have hη : 0 < A + N/2 - B := by linarith
  set η := A + N/2 - B with hηdef
  have hs0 : 0 < η / (N + η + 1) := by positivity
  have hs1 : η / (N + η + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  set s := η / (N + η + 1) with hsdef
  have hse : s * (N + η + 1) = η := by rw [hsdef]; field_simp
  have h3 := h s hs0 hs1
  have h4 : s * (A - B + (1-s)/2*N) ≤ 0 := by nlinarith [h3]
  have h5 : A - B + (1-s)/2*N ≤ 0 := by
    by_contra hc; push_neg at hc; nlinarith [mul_pos hs0 hc]
  nlinarith [mul_pos hs0 hs0]

lemma l6_closed {n : ℕ} {D : Set (TsengCGD.Global.Vec n)} {P : TsengCGD.Global.Vec n → ℝ} {K : ℝ}
    (hs : ProxNewton.Inexact.IsProperClosedConvex D P) (hL : PLipOn D P K) : IsClosed D := by
  classical
  obtain ⟨x0, hx0⟩ := hs.1
  apply isClosed_of_closure_subset
  intro z hz
  set M : ℝ := P x0 + K * (‖z - x0‖ + 1) with hM
  have hT := hs.2.2.2.isClosed_preimage (M : EReal)
  have hsub : D ∩ Metric.ball z 1 ⊆ (fun y => if y ∈ D then (P y : EReal) else ⊤) ⁻¹' Set.Iic (M : EReal) := by
    rintro y ⟨hyD, hyb⟩
    simp only [Set.mem_preimage, Set.mem_Iic, hyD, if_true]
    rw [EReal.coe_le_coe_iff]
    have h1 := hL.2 y hyD x0 hx0
    have h2 : ‖y - x0‖ ≤ ‖y - z‖ + ‖z - x0‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub y z x0
      exact this
    have h3 : ‖y - z‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hyb
    have hK := hL.1
    have := abs_le.mp h1
    nlinarith [this.2, mul_le_mul_of_nonneg_left (show ‖y - x0‖ ≤ ‖z - x0‖ + 1 by linarith) hK]
  have hz' : z ∈ closure (D ∩ Metric.ball z 1) := by
    rw [mem_closure_iff]
    intro o ho hzo
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hz (o ∩ Metric.ball z 1) (ho.inter Metric.isOpen_ball)
      ⟨hzo, Metric.mem_ball_self one_pos⟩
    exact ⟨y, hy1.1, hy2, hy1.2⟩
  have := closure_minimal hsub hT hz'
  by_contra hzD
  simp only [Set.mem_preimage, Set.mem_Iic, hzD, if_false] at this
  exact absurd this (by simp)


lemma l6_qf_one {n : ℕ} (d : TsengCGD.Global.Vec n) :
    TsengCGD.Global.qf (1 : Matrix (Fin n) (Fin n) ℝ) d = ‖d‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [TsengCGD.Global.qf, dotProduct, sq]

lemma l6_pair_ineq {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n))
    (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) (x : TsengCGD.Global.Vec n)
    (hD : Convex ℝ D) (hP : ConvexOn ℝ D P) (dt : TsengCGD.Global.Vec n) (δt : ℝ)
    (hs : IsEpiSubSol f D P c x (P x) dt δt) (d : TsengCGD.Global.Vec n) (δ : ℝ)
    (hd : x + d ∈ D) (hδ : P (x + d) ≤ P x + δ) :
    epiObj f c x dt δt + (‖d - dt‖^2 + (δ - δt)^2) / 2 ≤ epiObj f c x d δ := by
  apply l6_quad (by positivity)
  intro s hs0 hs1
  have hmem : x + (dt + s • (d - dt)) ∈ D := by
    have e : x + (dt + s • (d - dt)) = (1 - s) • (x + dt) + s • (x + d) := by module
    rw [e]
    exact hD hs.1 hd (by linarith) hs0.le (by ring)
  have hPle : P (x + (dt + s • (d - dt))) ≤ P x + (δt + s * (δ - δt)) := by
    have e : x + (dt + s • (d - dt)) = (1 - s) • (x + dt) + s • (x + d) := by module
    rw [e]
    have := hP.2 hs.1 hd (show 0 ≤ 1 - s by linarith) hs0.le (by ring)
    simp only [smul_eq_mul] at this
    have h2 := hs.2.1
    nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - s by linarith), mul_le_mul_of_nonneg_left hδ hs0.le]
  have hmin := hs.2.2 _ _ hmem hPle
  unfold epiObj at hmin ⊢
  rw [inner_add_right, inner_smul_right, inner_sub_right] at hmin
  have hsq := l6_sq_path dt d s
  have : (dt + s • (d - dt)) = dt + s • (d - dt) := rfl
  rw [hsq] at hmin
  nlinarith [hmin]

lemma l6_F1_ineq {n : ℕ} (g : TsengCGD.Global.Vec n) (c : ℝ) (D : Set (TsengCGD.Global.Vec n))
    (P : TsengCGD.Global.Vec n → ℝ) (x : TsengCGD.Global.Vec n)
    (hD : Convex ℝ D) (hP : ConvexOn ℝ D P) (hc : 0 ≤ c) (db : TsengCGD.Global.Vec n)
    (hdb : x + db ∈ D)
    (hmin : ∀ d', x + d' ∈ D → ⟪g, db⟫ + ‖db‖^2/2 + c * P (x + db) ≤ ⟪g, d'⟫ + ‖d'‖^2/2 + c * P (x + d'))
    (d : TsengCGD.Global.Vec n) (hd : x + d ∈ D) :
    ⟪g, db⟫ + ‖db‖^2/2 + c * P (x + db) + ‖d - db‖^2 / 2 ≤ ⟪g, d⟫ + ‖d‖^2/2 + c * P (x + d) := by
  have key : (⟪g, db⟫ + ‖db‖^2/2 + c * P (x + db)) + ‖d - db‖^2 / 2 ≤ ⟪g, d⟫ + ‖d‖^2/2 + c * P (x + d) := by
    apply l6_quad (A := ⟪g, db⟫ + ‖db‖^2/2 + c * P (x + db)) (N := ‖d - db‖^2) (by positivity)
    intro s hs0 hs1
    have e : x + (db + s • (d - db)) = (1 - s) • (x + db) + s • (x + d) := by module
    have hmem : x + (db + s • (d - db)) ∈ D := by
      rw [e]; exact hD hdb hd (by linarith) hs0.le (by ring)
    have hPle := hP.2 hdb hd (show 0 ≤ 1 - s by linarith) hs0.le (by ring)
    simp only [smul_eq_mul] at hPle
    rw [← e] at hPle
    have h1 := hmin _ hmem
    rw [inner_add_right, inner_smul_right, inner_sub_right] at h1
    have hsq := l6_sq_path db d s
    rw [hsq] at h1
    nlinarith [h1, mul_le_mul_of_nonneg_left hPle hc]
  exact key


lemma l6_exists {n : ℕ} (g : TsengCGD.Global.Vec n) (c K : ℝ) (hc : 0 < c)
    (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ)
    (hs : ProxNewton.Inexact.IsProperClosedConvex D P) (hL : PLipOn D P K)
    (x : TsengCGD.Global.Vec n) (hx : x ∈ D) :
    ∃ d, x + d ∈ D ∧ ∀ d', x + d' ∈ D →
      ⟪g, d⟫ + ‖d‖^2/2 + c * P (x + d) ≤ ⟪g, d'⟫ + ‖d'‖^2/2 + c * P (x + d') := by
  have hDc := l6_closed hs hL
  set R : ℝ := 2 * (‖g‖ + c * K) with hR
  set S : Set (TsengCGD.Global.Vec n) := {d | x + d ∈ D} with hS
  have hSc : IsClosed S := hDc.preimage (by fun_prop : Continuous fun d : TsengCGD.Global.Vec n => x + d)
  have hK : IsCompact (Metric.closedBall (0 : TsengCGD.Global.Vec n) R ∩ S) :=
    (isCompact_closedBall _ _).inter_right hSc
  have hne : (Metric.closedBall (0 : TsengCGD.Global.Vec n) R ∩ S).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
      have := hL.1
      positivity
    · simpa [hS] using hx
  have hPc : ContinuousOn P D := by
    have : LipschitzOnWith K.toNNReal P D := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL.1]
      exact hL.2 a ha b hb
    exact this.continuousOn
  have hcont : ContinuousOn (fun d : TsengCGD.Global.Vec n => ⟪g, d⟫ + ‖d‖^2/2 + c * P (x + d))
      (Metric.closedBall (0 : TsengCGD.Global.Vec n) R ∩ S) := by
    have h1 : ContinuousOn (fun d : TsengCGD.Global.Vec n => P (x + d)) S := by
      apply hPc.comp (by fun_prop : Continuous fun d : TsengCGD.Global.Vec n => x + d).continuousOn
      intro d hd; exact hd
    have h2 : ContinuousOn (fun d : TsengCGD.Global.Vec n => P (x + d))
        (Metric.closedBall (0 : TsengCGD.Global.Vec n) R ∩ S) := h1.mono Set.inter_subset_right
    have h3 : Continuous (fun d : TsengCGD.Global.Vec n => ⟪g, d⟫ + ‖d‖^2/2) := by fun_prop
    exact h3.continuousOn.add (h2.const_smul c)
  obtain ⟨dm, hdm, hmin⟩ := hK.exists_isMinOn hne hcont
  refine ⟨dm, hdm.2, ?_⟩
  intro d' hd'
  by_cases hb : ‖d'‖ ≤ R
  · exact hmin ⟨by simpa using hb, hd'⟩
  · push_neg at hb
    have h0 : (0 : TsengCGD.Global.Vec n) ∈ Metric.closedBall (0 : TsengCGD.Global.Vec n) R ∩ S := by
      obtain ⟨z, hz⟩ := hne
      have : z = 0 ∨ True := Or.inr trivial
      refine ⟨?_, by simpa [hS] using hx⟩
      simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
      have := hL.1
      positivity
    have hm0 : ⟪g, dm⟫ + ‖dm‖^2/2 + c * P (x + dm) ≤ ⟪g, (0 : TsengCGD.Global.Vec n)⟫ + ‖(0 : TsengCGD.Global.Vec n)‖^2/2 + c * P (x + 0) := hmin h0
    have hLip := hL.2 (x + d') hd' x hx
    have hnorm : ‖x + d' - x‖ = ‖d'‖ := by simp
    rw [hnorm] at hLip
    have hAbs := (abs_le.mp hLip).1
    have hcs : |⟪g, d'⟫| ≤ ‖g‖ * ‖d'‖ := abs_real_inner_le_norm g d'
    have hcs' := (abs_le.mp hcs).1
    have hK0 := hL.1
    simp only [inner_zero_right, norm_zero] at hm0
    have : ‖d'‖ * (‖d'‖/2 - ‖g‖ - c * K) ≥ 0 := by
      apply mul_nonneg (norm_nonneg _)
      rw [hR] at hb; linarith
    have hPx : P (x + 0) = P x := by simp
    rw [hPx] at hm0
    nlinarith [mul_le_mul_of_nonneg_left hAbs hc.le]


theorem l6_core : ∀ K : ℝ, 0 ≤ K → ∃ κ > 0, ∀ {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ),
      TsengCGD.Global.Standing f D P c → PLipOn D P K →
        ∀ x ∈ D, ∀ (dt : TsengCGD.Global.Vec n) (δt : ℝ), IsEpiSubSol f D P c x (P x) dt δt →
          pairNorm dt δt ≤ κ * ‖TsengCGD.Global.dI f D P c x‖ := by
  intro K hK
  refine ⟨1 + 2 * K, by linarith, ?_⟩
  intro n f D P c hs hL x hx dt δt hE
  obtain ⟨hDne, hDc, hPc, -⟩ := hs.properConvexLsc
  have hex := l6_exists (gradient f x) c K hs.c_pos D P hs.properConvexLsc hL x hx
  obtain ⟨dm, hdm1, hdm2⟩ := hex
  have hdir : TsengCGD.Global.IsDir f D P c 1 x Finset.univ (TsengCGD.Global.dI f D P c x) := by
    unfold TsengCGD.Global.dI TsengCGD.Global.dH
    apply Classical.epsilon_spec (p := TsengCGD.Global.IsDir f D P c 1 x Finset.univ)
    refine ⟨dm, fun j hj => absurd (Finset.mem_univ j) hj, hdm1, ?_⟩
    intro d' _ hd'
    unfold TsengCGD.Global.subObj
    rw [l6_qf_one, l6_qf_one]
    exact hdm2 d' hd'
  set db := TsengCGD.Global.dI f D P c x with hdb
  obtain ⟨-, hdb1, hdb2⟩ := hdir
  have hmin : ∀ d', x + d' ∈ D → inner ℝ (gradient f x) db + ‖db‖^2/2 + c * P (x + db) ≤
      inner ℝ (gradient f x) d' + ‖d'‖^2/2 + c * P (x + d') := by
    intro d' hd'
    have := hdb2 d' (fun j hj => absurd (Finset.mem_univ j) hj) hd'
    unfold TsengCGD.Global.subObj at this
    rwa [l6_qf_one, l6_qf_one] at this
  set δb : ℝ := P (x + db) - P x with hδb
  have h1 := l6_pair_ineq f D P c x hDc hPc dt δt hE db δb hdb1 (by rw [hδb]; linarith)
  have h2 := l6_F1_ineq (gradient f x) c D P x hDc hPc hs.c_pos.le db hdb1 hmin dt hE.1
  have h3 : c * (P (x + dt) - P x) ≤ c * δt := mul_le_mul_of_nonneg_left (by linarith [hE.2.1]) hs.c_pos.le
  unfold epiObj at h1
  have h4 : ‖db - dt‖^2 ≤ δb^2 / 2 := by
    have : ‖dt - db‖ = ‖db - dt‖ := norm_sub_rev _ _
    rw [this] at h2
    have hb : c * δb = c * P (x + db) - c * P x := by rw [hδb]; ring
    nlinarith [sq_nonneg (δb - δt), sq_nonneg δt]
  have h5 : δt^2 ≤ δb^2 := by
    have : ‖dt - db‖ = ‖db - dt‖ := norm_sub_rev _ _
    rw [this] at h2
    have hb : c * δb = c * P (x + db) - c * P x := by rw [hδb]; ring
    nlinarith [sq_nonneg (δb - δt), sq_nonneg ‖db - dt‖]
  have h6 : |δb| ≤ K * ‖db‖ := by
    have := hL.2 (x + db) hdb1 x hx
    simpa [hδb] using this
  have h7 : δb^2 ≤ (K * ‖db‖)^2 := by
    have := sq_abs δb
    nlinarith [abs_nonneg δb]
  have h8 : δt^2 ≤ (K * ‖db‖)^2 := le_trans h5 h7
  have h9 : ‖db - dt‖ ≤ K * ‖db‖ := by
    have h := abs_le_of_sq_le_sq (a := ‖db - dt‖) (b := K * ‖db‖) (by nlinarith) (by positivity)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  have h10 : ‖dt‖ ≤ (1 + K) * ‖db‖ := by
    have : ‖dt‖ = ‖db - (db - dt)‖ := by congr 1; abel
    rw [this]
    nlinarith [norm_sub_le db (db - dt)]
  unfold pairNorm
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hn : 0 ≤ ‖db‖ := norm_nonneg _
  have h11 : ‖dt‖^2 ≤ ((1 + K) * ‖db‖)^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) h10
  nlinarith [mul_nonneg hK hn, mul_nonneg (mul_nonneg hK hn) hn, mul_nonneg (mul_nonneg hK hn) (mul_nonneg hK hn)]

end TsengCGD.ErrorBound

open TsengCGD.ErrorBound


theorem solution :
    ∀ K : ℝ, 0 ≤ K → ∃ κ > 0, ∀ {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ),
      TsengCGD.Global.Standing f D P c → PLipOn D P K →
        ∀ x ∈ D, ∀ (dt : TsengCGD.Global.Vec n) (δt : ℝ), IsEpiSubSol f D P c x (P x) dt δt →
          pairNorm dt δt ≤ κ * ‖TsengCGD.Global.dI f D P c x‖ := by
  exact l6_core
