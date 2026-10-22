-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P17.adForwardDiagonalInput
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:35:51.300989+00:00
-- url     : https://prove2.me/submissions/52f60923-e1c3-47eb-8ab1-76b4809c6a44

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq


def g73h_F (r : ℝ) : ℝ := Real.log (1 + r) - Real.log (1 - r)

lemma g73h_F_series {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * r ^ (2 * k + 1)) (g73h_F r) :=
  Real.hasSum_log_sub_log_of_abs_lt_one (by rw [abs_of_nonneg h0]; exact h1)

lemma g73h_F_ge {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : 2 * r ≤ g73h_F r := by
  have := le_hasSum (g73h_F_series h0 h1) 0 (fun j _ => by positivity)
  simpa using this

lemma g73h_F_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : 0 ≤ g73h_F r := by
  linarith [g73h_F_ge h0 h1]

lemma g73h_F_neg (r : ℝ) : g73h_F (-r) = - g73h_F r := by
  unfold g73h_F; ring_nf

lemma g73h_psi_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    g73h_F a / a ≤ g73h_F b / b := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have sa := (g73h_F_series ha.le (lt_of_le_of_lt hab hb)).div_const a
  have sb := (g73h_F_series hb0.le hb).div_const b
  refine hasSum_le (fun k => ?_) sa sb
  have e1 : (2 : ℝ) * (1 / (2 * k + 1)) * a ^ (2 * k + 1) / a = 2 * (1 / (2 * k + 1)) * a ^ (2 * k) := by
    rw [pow_succ]; field_simp
  have e2 : (2 : ℝ) * (1 / (2 * k + 1)) * b ^ (2 * k + 1) / b = 2 * (1 / (2 * k + 1)) * b ^ (2 * k) := by
    rw [pow_succ]; field_simp
  rw [e1, e2]
  gcongr

/-- k(σ) = (1-σ) F(σ)/σ is antitone on (0,1). -/
lemma g73h_k_anti : AntitoneOn (fun σ : ℝ => (1 - σ) * g73h_F σ / σ) (Set.Ioo 0 1) := by
  have hderiv : ∀ σ ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun σ : ℝ => (1 - σ) * g73h_F σ / σ)
      ((-g73h_F σ + 2 * σ / (1 + σ)) / σ ^ 2) σ := by
    intro σ ⟨h0, h1⟩
    have hp : (0:ℝ) < 1 + σ := by linarith
    have hm : (0:ℝ) < 1 - σ := by linarith
    have hF : HasDerivAt g73h_F (1 / (1 + σ) + 1 / (1 - σ)) σ := by
      have a1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + σ)) σ := by
        have := ((hasDerivAt_id σ).const_add 1).log hp.ne'
        simpa using this
      have a2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - σ)) σ := by
        have := ((hasDerivAt_id σ).const_sub 1).log hm.ne'
        simpa [neg_div] using this
      unfold g73h_F
      exact (a1.sub a2).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) σ := by
      simpa using (hasDerivAt_id σ).const_sub 1
    refine ((h2.mul hF).div (hasDerivAt_id σ) h0.ne').congr_deriv ?_
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · intro x hx; exact (hderiv x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; intro x hx; exact (hderiv x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro x hx
    rw [(hderiv x hx).deriv]
    obtain ⟨h0, h1⟩ := hx
    have := g73h_F_ge h0.le h1
    have : 2 * x / (1 + x) ≤ 2 * x := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    linarith

lemma g73h_key {t m s : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (hm : 0 ≤ m) (hs0 : 0 < s) (hs1 : s < 1)
    (hs : s ^ 2 = t ^ 2 + 2 * (1 - t) * m) :
    (t - m) * g73h_F s / s ≤ g73h_F t := by
  have hFs := g73h_F_nonneg hs0.le hs1
  have hts : t ^ 2 ≤ s ^ 2 := by rw [hs]; nlinarith
  rcases lt_trichotomy t 0 with htn | htz | htp
  · -- t < 0
    set a := -t with ha
    have ha0 : 0 < a := by linarith
    have has : a ≤ s := by nlinarith
    have hmono := g73h_psi_mono ha0 has hs1
    have hFt : g73h_F t = - g73h_F a := by rw [ha, g73h_F_neg, neg_neg]
    rw [hFt]
    have hpa : 0 ≤ g73h_F a / a := div_nonneg (g73h_F_nonneg ha0.le (by linarith)) ha0.le
    have e1 : g73h_F a = a * (g73h_F a / a) := by field_simp
    have e2 : (t - m) * g73h_F s / s = -(a + m) * (g73h_F s / s) := by rw [ha]; ring
    rw [e2, e1]
    have : a * (g73h_F a / a) ≤ (a + m) * (g73h_F s / s) :=
      mul_le_mul (by linarith) hmono hpa (by linarith)
    linarith
  · subst htz
    simp only [g73h_F, add_zero, sub_zero, Real.log_one, sub_self]
    have : (0 - m) * (Real.log (1 + s) - Real.log (1 - s)) / s ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hs0.le
      have : 0 ≤ Real.log (1 + s) - Real.log (1 - s) := hFs
      nlinarith
    linarith
  · rcases le_or_gt t m with htm | htm
    · have : (t - m) * g73h_F s / s ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hs0.le
        nlinarith
      linarith [g73h_F_nonneg htp.le ht1]
    · -- t > m
      have hst : t ≤ s := by nlinarith
      have hk := g73h_k_anti ⟨htp, ht1⟩ ⟨hs0, hs1⟩ hst
      simp only at hk
      set c := 2 * t - t ^ 2 with hc
      have h1t : 0 < 1 - t := by linarith
      have h1s : 0 < 1 - s := by linarith
      have hcs : 0 ≤ c - s ^ 2 := by rw [hc, hs]; nlinarith
      have hratio : (c - s ^ 2) / (1 - s) ≤ (c - t ^ 2) / (1 - t) := by
        rw [div_le_div_iff₀ h1s h1t]; rw [hc]; nlinarith [sq_nonneg (s - t)]
      have hk0 : 0 ≤ (1 - s) * g73h_F s / s := div_nonneg (mul_nonneg h1s.le hFs) hs0.le
      have hprod := mul_le_mul hratio hk (hk0) (div_nonneg (by rw [hc]; nlinarith) h1t.le)
      have l1 : (c - s ^ 2) / (1 - s) * ((1 - s) * g73h_F s / s) = (c - s^2) * (g73h_F s / s) := by
        field_simp
      have l2 : (c - t ^ 2) / (1 - t) * ((1 - t) * g73h_F t / t) = (c - t^2) * (g73h_F t / t) := by
        field_simp
      rw [l1, l2] at hprod
      have e1 : (t - m) * g73h_F s / s = (c - s ^ 2) * (g73h_F s / s) / (2 * (1 - t)) := by
        have : t - m = (c - s ^ 2) / (2 * (1 - t)) := by
          rw [hc, hs]; field_simp; ring
        rw [this]; field_simp
      have e2 : g73h_F t = (c - t ^ 2) * (g73h_F t / t) / (2 * (1 - t)) := by
        rw [hc]; field_simp; ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_right hprod (by positivity)

def g73h_lam (m z : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * z * (1 - z - m))) / 2
def g73h_Phi (m z : ℝ) : ℝ := Real.binEntropy z - Real.binEntropy (g73h_lam m z)

lemma g73h_logF {w : ℝ} (h0 : -1 < w) (h1 : w < 1) :
    Real.log ((1 + w) / 2) - Real.log ((1 - w) / 2) = g73h_F w := by
  rw [Real.log_div (by linarith) (by norm_num), Real.log_div (by linarith) (by norm_num)]
  unfold g73h_F; ring

lemma g73h_Phi_zero {z : ℝ} : g73h_Phi 0 z = 0 := by
  unfold g73h_Phi g73h_lam
  have : 1 - 4 * z * (1 - z - 0) = (1 - 2 * z) ^ 2 := by ring
  rw [this, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 (1 - 2 * z) with h | h
  · rw [abs_of_nonneg h]; ring_nf
  · rw [abs_of_neg h]
    have : (1 - -(1 - 2 * z)) / 2 = 1 - z := by ring
    rw [this, Real.binEntropy_one_sub]; ring

lemma g73h_Phi_deriv {m z : ℝ} (hm0 : 0 < m) (hz0 : 0 < z) (hz1 : z < 1 - m) :
    HasDerivAt (g73h_Phi m) ((Real.log (1 - z) - Real.log z) -
      (Real.log (1 - g73h_lam m z) - Real.log (g73h_lam m z)) *
        (-((-4 * (1 - z - m) + 4 * z) / (2 * Real.sqrt (1 - 4 * z * (1 - z - m)))) / 2)) z := by
  have hu0 : 0 < 1 - 4 * z * (1 - z - m) := by nlinarith [sq_nonneg (1-2*z), mul_pos hz0 hm0]
  have hu1 : 1 - 4 * z * (1 - z - m) < 1 := by nlinarith
  have hs0 : 0 < Real.sqrt (1 - 4 * z * (1 - z - m)) := Real.sqrt_pos.2 hu0
  have hs1 : Real.sqrt (1 - 4 * z * (1 - z - m)) < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using hu1)
  have hu : HasDerivAt (fun z : ℝ => 1 - 4 * z * (1 - z - m)) (-4 * (1 - z - m) + 4 * z) z := by
    have := (((hasDerivAt_id z).const_mul 4).mul (((hasDerivAt_id z).const_sub 1).sub_const m)).const_sub 1
    refine this.congr_deriv ?_
    simp; ring
  have hs := hu.sqrt hu0.ne'
  have hl := (hs.const_sub 1).div_const 2
  have hl0 : g73h_lam m z ≠ 0 := by unfold g73h_lam; linarith
  have hl1 : g73h_lam m z ≠ 1 := by unfold g73h_lam; linarith
  have hb := (Real.hasDerivAt_binEntropy hl0 hl1).comp z hl
  have hz := Real.hasDerivAt_binEntropy hz0.ne' (by linarith : z ≠ 1)
  exact hz.sub hb

lemma g73h_Phi_mono {m y x : ℝ} (hm0 : 0 ≤ m) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ 1 - m) :
    g73h_Phi m y ≤ g73h_Phi m x := by
  rcases eq_or_lt_of_le hm0 with h | hm
  · subst h; rw [g73h_Phi_zero, g73h_Phi_zero]
  have hmono : MonotoneOn (g73h_Phi m) (Set.Icc 0 (1 - m)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact Continuous.continuousOn (by unfold g73h_Phi g73h_lam; fun_prop)
    · rw [interior_Icc]; intro z ⟨hz0, hz1⟩
      exact (g73h_Phi_deriv hm hz0 hz1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro z ⟨hz0, hz1⟩
      rw [(g73h_Phi_deriv hm hz0 hz1).deriv]
      set u := 1 - 4 * z * (1 - z - m) with hu
      have hu0 : 0 < u := by rw [hu]; nlinarith [sq_nonneg (1-2*z), mul_pos hz0 hm]
      have hu1 : u < 1 := by rw [hu]; nlinarith
      set s := Real.sqrt u with hsdef
      have hs0 : 0 < s := Real.sqrt_pos.2 hu0
      have hs1 : s < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using hu1)
      have hss : s ^ 2 = u := Real.sq_sqrt hu0.le
      set t := 1 - 2 * z with ht
      have hlam : g73h_lam m z = (1 - s) / 2 := rfl
      have e1 : Real.log (1 - z) - Real.log z = g73h_F t := by
        rw [← g73h_logF (by linarith) (by linarith)]; congr 2 <;> ring
      have e2 : Real.log (1 - g73h_lam m z) - Real.log (g73h_lam m z) = g73h_F s := by
        rw [hlam, ← g73h_logF (by linarith) hs1]; congr 2; ring
      have e3 : -((-4 * (1 - z - m) + 4 * z) / (2 * s)) / 2 = (t - m) / s := by
        rw [ht]; field_simp; ring
      rw [e1, e2, e3]
      have key := g73h_key (t := t) (m := m) (s := s) (by linarith) (by linarith) hm.le hs0 hs1
        (by rw [hss, hu, ht]; ring)
      have : g73h_F s * ((t - m) / s) = (t - m) * g73h_F s / s := by ring
      linarith
  rcases eq_or_lt_of_le hyx with h | h
  · rw [h]
  have hx' : 0 ≤ 1 - m := by linarith
  exact hmono ⟨hy, by linarith⟩ ⟨by linarith, hx⟩ hyx

lemma g73h_ad_apply (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    adChannel eta X = !![X 0 0 + (Real.sqrt (1-eta) : ℂ) * (Real.sqrt (1-eta) : ℂ) * X 1 1,
      (Real.sqrt eta : ℂ) * X 0 1; (Real.sqrt eta : ℂ) * X 1 0,
      (Real.sqrt eta : ℂ) * (Real.sqrt eta : ℂ) * X 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [adChannel, krausApply, adKraus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sum_apply,
    Matrix.conjTranspose_apply] <;> ring

lemma g73h_recv (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    receiverChannel (adDilation eta) X = adChannel eta X := by
  rw [g73h_ad_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [receiverChannel, traceRight, adDilation, adKraus, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply] <;> ring

lemma g73h_comp (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    complementaryChannel (adDilation eta) X = !![X 0 0 + (Real.sqrt eta : ℂ) * (Real.sqrt eta : ℂ) * X 1 1,
      (Real.sqrt (1-eta) : ℂ) * X 0 1; (Real.sqrt (1-eta) : ℂ) * X 1 0,
      (Real.sqrt (1-eta) : ℂ) * (Real.sqrt (1-eta) : ℂ) * X 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [complementaryChannel, traceLeft, adDilation, adKraus, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply] <;> ring

lemma g73h_sqC (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]


lemma g73h_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g73h_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g73h_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g73h_diag_herm d
  rw [g73h_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma g73h_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g73h_trace_cfc_diag]
  simp

lemma g73h_diag_eq (q : ℝ) : diagonalInput q = Matrix.diagonal (fun i => ((![1-q, q] : Fin 2 → ℝ) i : ℂ)) := by
  unfold diagonalInput; congr 1; funext i; fin_cases i <;> simp

lemma g73h_vn_diagInput (q : ℝ) : vnEntropy (diagonalInput q) = binEntropy2 q := by
  rw [g73h_diag_eq, g73h_vn_diag]
  simp [Fin.sum_univ_two, binEntropy2, Real.binEntropy, Real.logb, Real.log_inv]
  ring


lemma g73h_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

def g73h_ptr {Z X Y : Type*} [Fintype Y] (e : Z ≃ X × Y) (M : Matrix Z Z ℂ) : Matrix X X ℂ :=
  fun a b => ∑ r, M (e.symm (a, r)) (e.symm (b, r))

lemma g73h_ptr_herm {Z X Y : Type*} [Fintype Y] (e : Z ≃ X × Y) (M : Matrix Z Z ℂ)
    (hM : M.IsHermitian) : (g73h_ptr e M).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, g73h_ptr, star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Matrix.conjTranspose_apply, hM]

lemma g73h_CH (A : Matrix (Fin 2) (Fin 2) ℂ) (δ : ℂ) (htr : A 0 0 + A 1 1 = 1)
    (hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = δ) : A * A = A - δ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (A 0 0) * htr - hdet
  · linear_combination (A 0 1) * htr
  · linear_combination (A 1 0) * htr
  · linear_combination (A 1 1) * htr - hdet

lemma g73h_rec (A : Matrix (Fin 2) (Fin 2) ℂ) (δ : ℂ) (hA : A * A = A - δ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (k : ℕ) : (A ^ (k + 2)).trace = (A ^ (k + 1)).trace - δ * (A ^ k).trace := by
  have : A ^ (k + 2) = A ^ (k + 1) - δ • A ^ k := by
    rw [pow_add, sq, hA, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, pow_succ]
  rw [this, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

lemma g73h_trpow (A B : Matrix (Fin 2) (Fin 2) ℂ) (δ : ℂ)
    (hA1 : A 0 0 + A 1 1 = 1) (hA2 : A 0 0 * A 1 1 - A 0 1 * A 1 0 = δ)
    (hB1 : B 0 0 + B 1 1 = 1) (hB2 : B 0 0 * B 1 1 - B 0 1 * B 1 0 = δ) :
    ∀ k : ℕ, (A ^ (k + 1)).trace = (B ^ (k + 1)).trace := by
  have rA := g73h_rec A δ (g73h_CH A δ hA1 hA2)
  have rB := g73h_rec B δ (g73h_CH B δ hB1 hB2)
  have P : ∀ k : ℕ, (A ^ k).trace = (B ^ k).trace ∧ (A ^ (k + 1)).trace = (B ^ (k + 1)).trace := by
    intro k
    induction k with
    | zero => refine ⟨by simp, ?_⟩; simp [Matrix.trace_fin_two, hA1, hB1]
    | succ k ih => exact ⟨ih.2, by rw [rA, rB, ih.1, ih.2]⟩
  exact fun k => (P k).2

lemma g73h_vn2 (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z)
    (htr : M 0 0 + M 1 1 = 1) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = ((z * (1 - z - m) : ℝ) : ℂ)) :
    vnEntropy M = binEntropy2 (g73h_lam m z) := by
  set l := g73h_lam m z with hl
  have hu : 0 ≤ 1 - 4 * z * (1 - z - m) := by nlinarith [sq_nonneg (1 - 2 * z), mul_nonneg hz hm]
  have hss := Real.sq_sqrt hu
  have hD : (diagonalInput l).IsHermitian := by rw [g73h_diag_eq]; exact g73h_diag_herm _
  have hD1 : diagonalInput l 0 0 + diagonalInput l 1 1 = 1 := by simp [diagonalInput]
  have hD2 : diagonalInput l 0 0 * diagonalInput l 1 1 - diagonalInput l 0 1 * diagonalInput l 1 0 =
      ((z * (1 - z - m) : ℝ) : ℂ) := by
    simp only [diagonalInput, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, sub_zero]
    rw [← Complex.ofReal_mul]
    congr 1
    rw [hl, g73h_lam]
    nlinarith [hss]
  have h := g73h_trace_cfc_eq M (diagonalInput l) hM hD (fun x : ℝ => x * Real.logb 2 x) (by simp)
    (g73h_trpow M _ _ htr hdet hD1 hD2)
  have h2 := g73h_vn_diagInput l
  unfold vnEntropy at h2 ⊢
  rw [h]; exact h2

lemma g73h_recv_herm (V : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.IsHermitian) :
    (receiverChannel V G).IsHermitian := by
  have hM : (V * G * Vᴴ).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V hG
  have : receiverChannel V G = g73h_ptr (Equiv.refl _) (V * G * Vᴴ) := by ext a b; rfl
  rw [this]; exact g73h_ptr_herm _ _ hM

lemma g73h_comp_herm (V : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.IsHermitian) :
    (complementaryChannel V G).IsHermitian := by
  have hM : (V * G * Vᴴ).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V hG
  have : complementaryChannel V G = g73h_ptr (Equiv.prodComm (Fin 2) (Fin 2)).symm (V * G * Vᴴ) := by
    ext a b; rfl
  rw [this]; exact g73h_ptr_herm _ _ hM

lemma g73h_fwd (eta p m : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hp : 0 ≤ p) (hm : 0 ≤ m)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.IsHermitian) (h00 : G 0 0 = ((1 - p : ℝ) : ℂ))
    (h11 : G 1 1 = (p : ℂ)) (h01 : G 0 1 * G 1 0 = ((p * m : ℝ) : ℂ)) :
    forwardInfo (adDilation eta) G =
      binEntropy2 (g73h_lam m (eta * p)) - binEntropy2 (g73h_lam m ((1 - eta) * p)) := by
  have a := g73h_sqC eta h0
  have b := g73h_sqC (1 - eta) (by linarith)
  unfold forwardInfo
  have e1 := g73h_vn2 (receiverChannel (adDilation eta) G) (g73h_recv_herm _ _ hG) m (eta * p) hm
    (mul_nonneg h0 hp) (by
      rw [g73h_recv, g73h_ad_apply]; simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [a, b, h00, h11]; push_cast; ring) (by
      rw [g73h_recv, g73h_ad_apply]; simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      have : (Real.sqrt eta : ℂ) * G 0 1 * ((Real.sqrt eta : ℂ) * G 1 0) =
          (Real.sqrt eta : ℂ) * (Real.sqrt eta : ℂ) * (G 0 1 * G 1 0) := by ring
      rw [this, a, b, h00, h11, h01]; push_cast; ring)
  have e2 := g73h_vn2 (complementaryChannel (adDilation eta) G) (g73h_comp_herm _ _ hG) m ((1 - eta) * p) hm
    (mul_nonneg (by linarith) hp) (by
      rw [g73h_comp]; simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [a, b, h00, h11]; push_cast; ring) (by
      rw [g73h_comp]; simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      have : (Real.sqrt (1 - eta) : ℂ) * G 0 1 * ((Real.sqrt (1 - eta) : ℂ) * G 1 0) =
          (Real.sqrt (1 - eta) : ℂ) * (Real.sqrt (1 - eta) : ℂ) * (G 0 1 * G 1 0) := by ring
      rw [this, a, b, h00, h11, h01]; push_cast; ring)
  rw [e1, e2]

lemma g73h_gen (p theta phi : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (generalInput p theta phi).IsHermitian ∧
    generalInput p theta phi 0 0 = ((1 - p : ℝ) : ℂ) ∧
    generalInput p theta phi 1 1 = (p : ℂ) ∧
    generalInput p theta phi 0 1 * generalInput p theta phi 1 0 =
      ((p * ((1 - p) * Real.cos theta ^ 2) : ℝ) : ℂ) := by
  have hpd : (pureDensity (inputPurification p theta phi)).IsHermitian := by
    ext a b; simp [pureDensity, mul_comm]
  have hH : (generalInput p theta phi).IsHermitian := by
    have : generalInput p theta phi =
        g73h_ptr (Equiv.prodComm (Fin 2) (Fin 2)).symm (pureDensity (inputPurification p theta phi)) := by
      ext a b; rfl
    rw [this]; exact g73h_ptr_herm _ _ hpd
  have hn : ∀ z : ℂ, z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := fun z => Complex.mul_conj z
  have hE : Complex.normSq (Complex.exp (Complex.I * (phi : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, mul_comm, Complex.norm_exp_ofReal_mul_I]; norm_num
  have q00 : (inputPurification p theta phi) (0, 0) = (Real.sqrt (1 - p) : ℂ) := by
    simp [inputPurification]
  have q10 : (inputPurification p theta phi) (1, 0) = 0 := by
    simp [inputPurification]
  have q01 : (inputPurification p theta phi) (0, 1) =
      (Real.sqrt p : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) * ((Real.cos theta : ℝ) : ℂ) := by
    simp only [inputPurification, PiLp.toLp_apply]; simp
  have q11 : (inputPurification p theta phi) (1, 1) =
      (Real.sqrt p : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) * ((Real.sin theta : ℝ) : ℂ) := by
    simp only [inputPurification, PiLp.toLp_apply]; simp
  have G : ∀ a b, generalInput p theta phi a b =
      inputPurification p theta phi (0, a) * (starRingEnd ℂ) (inputPurification p theta phi (0, b)) +
      inputPurification p theta phi (1, a) * (starRingEnd ℂ) (inputPurification p theta phi (1, b)) := by
    intro a b; simp only [generalInput, traceLeft, pureDensity, Matrix.of_apply, Fin.sum_univ_two]
  have h01 : generalInput p theta phi 0 1 = (Real.sqrt (1 - p) : ℂ) *
      (starRingEnd ℂ) ((Real.sqrt p : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) * ((Real.cos theta : ℝ) : ℂ)) := by
    rw [G, q00, q01, q10]; ring
  refine ⟨hH, ?_, ?_, ?_⟩
  · rw [G, q00, q10, hn, Complex.normSq_ofReal, Real.mul_self_sqrt (by linarith)]; simp
  · rw [G, q01, q11, hn, hn]
    simp only [Complex.normSq_mul, Complex.normSq_ofReal, hE, Real.mul_self_sqrt hp0]
    have := Real.cos_sq_add_sin_sq theta
    rw [← Complex.ofReal_add]
    congr 1
    linear_combination p * this
  · have h10 : generalInput p theta phi 1 0 = (starRingEnd ℂ) (generalInput p theta phi 0 1) := by
      have := hH.apply 1 0
      rw [← this]; rfl
    rw [h10, hn, h01]
    simp only [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_ofReal, hE,
      Real.mul_self_sqrt hp0, Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ 1 - p)]
    congr 1; ring

/-- PDF p.5: at fixed excited population, a diagonal input maximizes forward
information for degradable AD, in the eta>1/2 regime explicitly used by the proof. -/
theorem solution (eta p theta phi : ℝ)
    (heta : eta ∈ Set.Ioc (1/2 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    forwardInfo (adDilation eta) (generalInput p theta phi) ≤
      forwardInfo (adDilation eta) (diagonalInput p) := by
  obtain ⟨he0, he1⟩ := heta
  obtain ⟨hp0, hp1⟩ := hp
  have h0 : 0 ≤ eta := by linarith
  obtain ⟨hH, g00, g11, g01⟩ := g73h_gen p theta phi hp0 hp1
  set m := (1 - p) * Real.cos theta ^ 2 with hm
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 - p := by
    have := Real.cos_sq_le_one theta
    rw [hm]; nlinarith
  rw [g73h_fwd eta p m h0 he1 hp0 hm0 _ hH g00 g11 g01]
  have hD : (diagonalInput p).IsHermitian := by rw [g73h_diag_eq]; exact g73h_diag_herm _
  rw [g73h_fwd eta p 0 h0 he1 hp0 le_rfl _ hD (by simp [diagonalInput]) (by simp [diagonalInput])
    (by simp [diagonalInput])]
  have hmono := g73h_Phi_mono (m := m) (y := (1 - eta) * p) (x := eta * p) hm0
    (mul_nonneg (by linarith) hp0) (by nlinarith) (by nlinarith)
  have z1 := @g73h_Phi_zero (eta * p)
  have z2 := @g73h_Phi_zero ((1 - eta) * p)
  unfold g73h_Phi at hmono z1 z2
  unfold binEntropy2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_sub_div_same, div_sub_div_same]
  apply div_le_div_of_nonneg_right _ hl.le
  linarith



end
