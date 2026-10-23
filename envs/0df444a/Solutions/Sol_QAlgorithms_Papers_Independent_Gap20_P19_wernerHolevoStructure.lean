-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.wernerHolevoStructure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:45:19.070494+00:00
-- url     : https://prove2.me/submissions/e126f64e-d106-4e63-ac45-51188ea64e2d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Matrix

namespace QAlgorithms.Papers.Independent.Gap20.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Integer Levi-Civita isometry, `wernerIsometry = (√2)⁻¹ • x8W0`. -/
def x8W0 : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  Matrix.of fun p k => if p.1=p.2 ∨ p.1=k ∨ p.2=k then 0
    else if (p.1.val+1)%3=p.2.val then 1 else -1

lemma x8_W_eq : wernerIsometry = ((Real.sqrt 2 : ℂ)⁻¹) • x8W0 := by
  ext p k
  simp only [Matrix.smul_apply, x8W0, Matrix.of_apply, wernerIsometry]
  by_cases h1 : (p.1=p.2 ∨ p.1=k ∨ p.2=k) <;> by_cases h2 : (p.1.val+1)%3=p.2.val <;>
    simp [h1, h2]

lemma x8_s2 : ((Real.sqrt 2 : ℂ)⁻¹) * conj ((Real.sqrt 2 : ℂ)⁻¹) = 1/2 := by
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma x8_W0_iso : x8W0ᴴ * x8W0 = (2 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [x8W0, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, one_apply] <;> norm_num

lemma x8_W_iso : IsIsometry wernerIsometry := by
  unfold IsIsometry
  rw [x8_W_eq, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, x8_W0_iso,
    smul_smul]
  rw [show star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ * 2 = 1 by
    rw [Complex.star_def, mul_comm (conj _), x8_s2]; norm_num, one_smul]

lemma x8_recv_W0 (rho : Matrix (Fin 3) (Fin 3) ℂ) :
    receiverChannel x8W0 rho = rho.trace • 1 - rhoᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [receiverChannel, QAlgorithms.traceRight, x8W0, mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_three, one_apply, Matrix.trace] <;> ring

lemma x8_comp_W0 (rho : Matrix (Fin 3) (Fin 3) ℂ) :
    complementaryChannel x8W0 rho = rho.trace • 1 - rhoᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complementaryChannel, QAlgorithms.traceLeft, x8W0, mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_three, one_apply, Matrix.trace] <;> ring

lemma x8_WH3 (rho : Matrix (Fin 3) (Fin 3) ℂ) :
    wernerHolevo 3 rho = ((Real.sqrt 2 : ℂ)⁻¹ * conj ((Real.sqrt 2 : ℂ)⁻¹)) •
      (rho.trace • 1 - rhoᵀ) := by
  rw [x8_s2, wernerHolevo]
  norm_num

lemma x8_scale {A B E : Type} [Fintype A] [Fintype B] [Fintype E] (c : ℂ)
    (V : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) :
    receiverChannel (c • V) rho = (c * conj c) • receiverChannel V rho ∧
    complementaryChannel (c • V) rho = (c * conj c) • complementaryChannel V rho := by
  constructor
  · ext i j
    simp [receiverChannel, QAlgorithms.traceRight, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · ext i j
    simp [complementaryChannel, QAlgorithms.traceLeft, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma x8_W_recv : receiverChannel wernerIsometry = wernerHolevo 3 := by
  funext rho
  rw [x8_W_eq, (x8_scale _ _ _).1, x8_recv_W0, x8_WH3]

lemma x8_W_comp : complementaryChannel wernerIsometry = wernerHolevo 3 := by
  funext rho
  rw [x8_W_eq, (x8_scale _ _ _).2, x8_comp_W0, x8_WH3]

lemma x8_proj_rank {d : ℕ} (w : Fin d → ℂ) (hw : star w ⬝ᵥ w = 1) :
    ((1 : Matrix (Fin d) (Fin d) ℂ) - vecMulVec w (star w)).rank = d - 1 := by
  set Q := (1 : Matrix (Fin d) (Fin d) ℂ) - vecMulVec w (star w)
  have hQ : ∀ x, Q *ᵥ x = x - (star w ⬝ᵥ x) • w := by
    intro x
    simp only [Q, sub_mulVec, one_mulVec, vecMulVec_mulVec]
    congr 1
    ext i; simp [mul_comm]
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hker : LinearMap.ker Q.mulVecLin = ℂ ∙ w := by
    ext x
    rw [LinearMap.mem_ker, mulVecLin_apply, hQ, Submodule.mem_span_singleton, sub_eq_zero]
    constructor
    · intro h; exact ⟨_, h.symm⟩
    · rintro ⟨c, rfl⟩
      rw [dotProduct_smul, hw, smul_eq_mul, mul_one]
  have h := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
  rw [hker, finrank_span_singleton hw0, Module.finrank_fin_fun] at h
  change Q.rank + 1 = d at h
  omega

lemma x8_WH_rank (d : ℕ) (hd : 1 < d) (psi : EuclideanSpace ℂ (Fin d)) (hpsi : IsState psi) :
    (wernerHolevo d (pureDensity psi)).rank = d - 1 := by
  have htr : (pureDensity psi).trace = 1 := by
    have h1 : ‖psi‖ = 1 := hpsi
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) psi
    rw [h1, PiLp.inner_apply] at h2
    simp only [RCLike.inner_apply, one_pow, map_one] at h2
    rw [← h2]
    simp [Matrix.trace, QAlgorithms.pureDensity, mul_comm]
  have hT : (pureDensity psi)ᵀ = vecMulVec (star fun i => psi i) (star (star fun i => psi i)) := by
    ext i j; simp [QAlgorithms.pureDensity, vecMulVec_apply, mul_comm]
  have hw : star (star fun i => psi i) ⬝ᵥ (star fun i => psi i) = 1 := by
    rw [star_star, ← htr]
    simp [Matrix.trace, QAlgorithms.pureDensity, dotProduct]
  have hc : ((d : ℂ) - 1)⁻¹ ∈ nonZeroDivisors ℂ := by
    apply mem_nonZeroDivisors_of_ne_zero
    apply inv_ne_zero
    rw [sub_ne_zero]
    exact_mod_cast hd.ne'
  rw [wernerHolevo, rank_smul_of_mem_nonZeroDivisors _ hc, htr, one_smul, hT]
  exact x8_proj_rank _ hw

lemma x8_kraus_single {m : ℕ} (L : Fin m → Matrix (Fin 3) (Fin 3) ℂ) (x y u v : Fin 3) :
    (∑ k, L k * Matrix.single x y (1 : ℂ) * (L k)ᴴ) u v = ∑ k, L k u x * conj (L k v y) := by
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Matrix.single_apply, Fin.sum_univ_three]

lemma x8_S {m : ℕ} (L : Fin m → Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3) :
    let N := fun r : Matrix (Fin 3) (Fin 3) ℂ => ∑ k, L k * r * (L k)ᴴ
    N (Matrix.single b b 1) a a + N (Matrix.single b a 1) a b + N (Matrix.single a b 1) b a +
      N (Matrix.single a a 1) b b = ((∑ k, Complex.normSq (L k a b + L k b a) : ℝ) : ℂ) := by
  intro N
  simp only [N, x8_kraus_single, ← Finset.sum_add_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_add]
  ring

lemma x8_S_WH (a b : Fin 3) :
    wernerHolevo 3 (Matrix.single b b 1) a a + wernerHolevo 3 (Matrix.single b a 1) a b +
      wernerHolevo 3 (Matrix.single a b 1) b a + wernerHolevo 3 (Matrix.single a a 1) b b = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [wernerHolevo, Matrix.single_apply, one_apply, Matrix.trace, Fin.sum_univ_three] <;> ring

lemma x8_antisym_eval {m : ℕ} (L : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hTP : ∑ k, (L k)ᴴ * L k = 1) (hanti : ∀ k a b, L k a b + L k b a = 0)
    (rho : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ k, L k * rho * (L k)ᴴ = (1/2 : ℂ) • (rho.trace • 1 - rhoᵀ) := by
  set x : Fin m → ℂ := fun k => L k 0 1
  set y : Fin m → ℂ := fun k => L k 0 2
  set z : Fin m → ℂ := fun k => L k 1 2
  have hL : ∀ k, L k = !![0, x k, y k; -x k, 0, z k; -y k, -z k, 0] := by
    intro k
    ext a b
    have h := hanti k
    fin_cases a <;> fin_cases b <;> simp [x, y, z]
    all_goals first
      | (have := h 0 0; linear_combination this / 2)
      | (have := h 1 1; linear_combination this / 2)
      | (have := h 2 2; linear_combination this / 2)
      | (have := h 1 0; linear_combination this)
      | (have := h 2 0; linear_combination this)
      | (have := h 2 1; linear_combination this)
  have hT : ∀ i j, ∑ k, ((L k)ᴴ * L k) i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
    intro i j; rw [← hTP, Matrix.sum_apply]
  simp only [hL] at hT
  have t00 := hT 0 0
  have t11 := hT 1 1
  have t22 := hT 2 2
  have t01 := hT 0 1
  have t02 := hT 0 2
  have t12 := hT 1 2
  simp [mul_apply, Fin.sum_univ_three, Finset.sum_add_distrib] at t00 t11 t22 t01 t02 t12
  have sw : ∀ u v : Fin m → ℂ, ∑ k, conj (u k) * v k = ∑ k, v k * conj (u k) :=
    fun u v => Finset.sum_congr rfl fun k _ => mul_comm _ _
  have cj : ∀ u v : Fin m → ℂ, ∑ k, conj (u k) * v k = 0 → ∑ k, u k * conj (v k) = 0 := by
    intro u v h
    have := congrArg conj h
    simpa [map_sum, mul_comm] using this
  have xx : ∑ k, x k * conj (x k) = 1/2 := by
    rw [← sw]; linear_combination (t00 + t11 - t22) / 2
  have yy : ∑ k, y k * conj (y k) = 1/2 := by
    rw [← sw]; linear_combination (t00 - t11 + t22) / 2
  have zz : ∑ k, z k * conj (z k) = 1/2 := by
    rw [← sw]; linear_combination (- t00 + t11 + t22) / 2
  have yz : ∑ k, z k * conj (y k) = 0 := by rw [← sw]; exact t01
  have xz : ∑ k, z k * conj (x k) = 0 := by rw [← sw]; exact t02
  have xy : ∑ k, y k * conj (x k) = 0 := by rw [← sw]; exact t12
  have zy : ∑ k, y k * conj (z k) = 0 := cj _ _ t01
  have zx : ∑ k, x k * conj (z k) = 0 := cj _ _ t02
  have yx : ∑ k, x k * conj (y k) = 0 := cj _ _ t12
  have hG : ∀ i a j b, ∑ k, L k i a * conj (L k j b) =
      ((if i = j ∧ a = b then 1 else 0) - (if i = b ∧ a = j then 1 else 0)) / 2 := by
    intro i a j b
    simp only [hL]
    fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
      simp [neg_mul, mul_neg, Finset.sum_neg_distrib, xx, yy, zz, yz, xz, xy, zy, zx, yx] <;> norm_num
  ext i j
  rw [Matrix.sum_apply]
  have hexp : ∀ k, (L k * rho * (L k)ᴴ) i j = ∑ a, ∑ b, rho a b * (L k i a * conj (L k j b)) := by
    intro k
    simp only [mul_apply, conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp only [hexp]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (s := Finset.univ (α := Fin m)), ← Finset.mul_sum, hG]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, Matrix.trace, one_apply] <;> ring

lemma x8_isChannel_of {I O κ : Type} [Fintype I] [Fintype O] [DecidableEq I] [Fintype κ]
    (Phi : QAlgorithms.Superop I O) (F : κ → Matrix O I ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1)
    (hPhi : ∀ X, Phi X = ∑ k, F k * X * (F k)ᴴ) : QAlgorithms.IsChannel Phi := by
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun n => F (e.symm n), ?_, fun X => ?_⟩
  · unfold QAlgorithms.IsKrausFamily; rw [← hF, ← e.symm.sum_comp]
  · rw [hPhi X, QAlgorithms.krausApply, ← e.symm.sum_comp]

lemma x8_recv_kraus {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (V : Matrix (B × E) A ℂ) :
    (∀ X, receiverChannel V X = ∑ e, (Matrix.of fun b a => V (b, e) a) * X *
      (Matrix.of fun b a => V (b, e) a)ᴴ) ∧
    ∑ e, (Matrix.of fun b a => V (b, e) a)ᴴ * (Matrix.of fun b a => V (b, e) a) = Vᴴ * V := by
  constructor
  · intro X
    ext b b'
    simp [receiverChannel, QAlgorithms.traceRight, mul_apply, Matrix.sum_apply,
      Fintype.sum_prod_type]
  · ext a a'
    simp [mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
    exact Finset.sum_comm

lemma x8_WH_channel : QAlgorithms.IsChannel (wernerHolevo 3) := by
  obtain ⟨h1, h2⟩ := x8_recv_kraus wernerIsometry
  refine x8_isChannel_of _ _ (by rw [h2]; exact x8_W_iso) fun X => ?_
  rw [← h1, x8_W_recv]

lemma x8_id_channel {I : Type} [Fintype I] [DecidableEq I] :
    QAlgorithms.IsChannel (fun r : Matrix I I ℂ => r) :=
  x8_isChannel_of _ (fun _ : Unit => (1 : Matrix I I ℂ)) (by simp) (fun X => by simp)

lemma x8_core (N M : QAlgorithms.Superop (Fin 3) (Fin 3)) (hN : QAlgorithms.IsChannel N)
    (hM : QAlgorithms.IsChannel M) (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (h : ∀ r, wernerHolevo 3 r = (p : ℂ) • N r + (q : ℂ) • M r) : N = wernerHolevo 3 := by
  obtain ⟨m, L, hLK, hNL⟩ := hN
  obtain ⟨m', R, -, hMR⟩ := hM
  have hNe : ∀ r, N r = ∑ k, L k * r * (L k)ᴴ := hNL
  have hMe : ∀ r, M r = ∑ k, R k * r * (R k)ᴴ := hMR
  have hanti : ∀ k a b, L k a b + L k b a = 0 := by
    intro k a b
    have hS := x8_S_WH a b
    simp only [h, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hNe, hMe] at hS
    have e1 := x8_S L a b
    have e2 := x8_S R a b
    simp only at e1 e2
    have hS' : (p : ℂ) * ((∑ k, Complex.normSq (L k a b + L k b a) : ℝ) : ℂ) +
        (q : ℂ) * ((∑ k, Complex.normSq (R k a b + R k b a) : ℝ) : ℂ) = 0 := by
      rw [← e1, ← e2]; linear_combination hS
    have hS'' : p * (∑ k, Complex.normSq (L k a b + L k b a)) +
        q * (∑ k, Complex.normSq (R k a b + R k b a)) = 0 := by exact_mod_cast hS'
    have n1 : 0 ≤ ∑ k, Complex.normSq (L k a b + L k b a) :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have n2 : 0 ≤ ∑ k, Complex.normSq (R k a b + R k b a) :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have z1 : ∑ k, Complex.normSq (L k a b + L k b a) = 0 := by
      have : p * (∑ k, Complex.normSq (L k a b + L k b a)) = 0 := by
        nlinarith [mul_nonneg hp.le n1, mul_nonneg hq n2]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hp.ne'
      · exact h0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg
      (L k a b + L k b a))).1 z1 k (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp this
  funext r
  rw [hNe, x8_antisym_eval L hLK hanti, x8_WH3, x8_s2]

lemma x8_extreme : ExtremeIn QAlgorithms.IsChannel (wernerHolevo 3) := by
  refine ⟨x8_WH_channel, fun N M p hN hM hp hp1 hPhi => ⟨?_, ?_⟩⟩
  · exact x8_core N M hN hM p (1 - p) hp (by linarith) fun r => congrFun hPhi r
  · refine x8_core M N hM hN (1 - p) p (by linarith) hp.le fun r => ?_
    rw [congrFun hPhi r, add_comm]

theorem x8_wmain :
    (∀ d : ℕ, 1 < d → ∀ psi : EuclideanSpace ℂ (Fin d), IsState psi →
      (wernerHolevo d (pureDensity psi)).rank = d-1) ∧
    IsIsometry wernerIsometry ∧ receiverChannel wernerIsometry = wernerHolevo 3 ∧
    complementaryChannel wernerIsometry = wernerHolevo 3 ∧
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (wernerHolevo 3) ∧ IsDegradable witness) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (wernerHolevo 3) ∧ IsAntidegradable witness) ∧
    ExtremeIn IsChannel (wernerHolevo 3) :=
  ⟨x8_WH_rank, x8_W_iso, x8_W_recv, x8_W_comp,
    ⟨3, wernerIsometry, x8_W_recv, x8_W_iso, fun r => r, x8_id_channel,
      fun rho => by rw [x8_W_comp, x8_W_recv]⟩,
    ⟨3, wernerIsometry, x8_W_recv, x8_W_iso, fun r => r, x8_id_channel,
      fun rho => by rw [x8_W_comp, x8_W_recv]⟩,
    x8_extreme⟩

end QAlgorithms.Papers.Independent.Gap20.P19



open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P19 in
/-- Section 2.2, PDF p.10: pure-output rank in every d>1 and the specific
self-complementary extreme Werner–Holevo qutrit channel. The complement is tied
to its antisymmetric Levi-Civita isometry, not freely selected. -/
theorem solution :
    (∀ d : ℕ, 1 < d → ∀ psi : EuclideanSpace ℂ (Fin d), IsState psi →
      (wernerHolevo d (pureDensity psi)).rank = d-1) ∧
    IsIsometry wernerIsometry ∧ receiverChannel wernerIsometry = wernerHolevo 3 ∧
    complementaryChannel wernerIsometry = wernerHolevo 3 ∧
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (wernerHolevo 3) ∧ IsDegradable witness) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (wernerHolevo 3) ∧ IsAntidegradable witness) ∧
    ExtremeIn IsChannel (wernerHolevo 3) :=
  x8_wmain



