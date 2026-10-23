-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P23.zeroErrorGraphInvariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:19:13.953577+00:00
-- url     : https://prove2.me/submissions/02941373-d74b-415d-91b3-da7f5140784c

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

set_option linter.unusedSectionVars false

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def x8vec (X : Matrix B A ℂ) : A × B → ℂ := fun p => X p.2 p.1

def x8ip (u x : A × B → ℂ) : ℂ := ∑ p, conj (x p) * u p

def x8Q (J : Matrix (A × B) (A × B) ℂ) (x : A × B → ℂ) : ℂ :=
  ∑ p, ∑ q, conj (x p) * J p q * x q

lemma x8_choi_kraus {m : ℕ} (E : Fin m → Matrix B A ℂ) (N : Superop A B)
    (hN : ∀ ρ, N ρ = krausApply E ρ) :
    choi N = ∑ i, Matrix.vecMulVec (x8vec (E i)) (star (x8vec (E i))) := by
  ext p q
  simp only [choi, hN, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    x8vec, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Pi.star_apply, ite_and]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma x8_Q_rank1 (u x : A × B → ℂ) :
    x8Q (Matrix.vecMulVec u (star u)) x = ((‖x8ip u x‖ ^ 2 : ℝ) : ℂ) := by
  have : x8Q (Matrix.vecMulVec u (star u)) x = x8ip u x * conj (x8ip u x) := by
    unfold x8Q x8ip
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, map_mul,
      Complex.conj_conj]
    ring
  rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma x8_Q_sum {m : ℕ} (J : Fin m → Matrix (A × B) (A × B) ℂ) (x : A × B → ℂ) :
    x8Q (∑ i, J i) x = ∑ i, x8Q (J i) x := by
  unfold x8Q
  simp only [Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

lemma x8_Q_choi_re {m : ℕ} (E : Fin m → Matrix B A ℂ) (N : Superop A B)
    (hN : ∀ ρ, N ρ = krausApply E ρ) (x : A × B → ℂ) :
    (x8Q (choi N) x).re = ∑ i, ‖x8ip (x8vec (E i)) x‖ ^ 2 := by
  rw [x8_choi_kraus E N hN, x8_Q_sum, Complex.re_sum]
  simp only [x8_Q_rank1, Complex.ofReal_re]

lemma x8_Q_choi_nonneg (N : Superop A B) (hN : IsChannel N) (x : A × B → ℂ) :
    0 ≤ (x8Q (choi N) x).re := by
  obtain ⟨m, E, -, hE⟩ := hN
  rw [x8_Q_choi_re E N hE]; positivity

lemma x8_vec_add (X Y : Matrix B A ℂ) : x8vec (X + Y) = x8vec X + x8vec Y := rfl

lemma x8_ip_add (u v x : A × B → ℂ) : x8ip (u + v) x = x8ip u x + x8ip v x := by
  simp [x8ip, mul_add, Finset.sum_add_distrib]

lemma x8_ip_smul (c : ℂ) (u x : A × B → ℂ) : x8ip (c • u) x = c * x8ip u x := by
  simp [x8ip, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring

lemma x8_gen_bound (N : Superop A B) (X : Matrix B A ℂ) (hX : X ∈ bipartiteGraph N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x8ip (x8vec X) x‖ ^ 2 ≤ C * (x8Q (choi N) x).re := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨k, F, -, hF, i, rfl⟩ := hX
    refine ⟨1, zero_le_one, fun x => ?_⟩
    rw [one_mul, x8_Q_choi_re F N hF]
    exact Finset.single_le_sum (f := fun j => ‖x8ip (x8vec (F j)) x‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  | zero =>
    refine ⟨0, le_rfl, fun x => ?_⟩
    simp [x8ip, x8vec]
  | add X Y _ _ hX hY =>
    obtain ⟨C1, hC1, h1⟩ := hX
    obtain ⟨C2, hC2, h2⟩ := hY
    refine ⟨2 * C1 + 2 * C2, by positivity, fun x => ?_⟩
    rw [x8_vec_add, x8_ip_add]
    have ht := norm_add_le (x8ip (x8vec X) x) (x8ip (x8vec Y) x)
    have hn1 := norm_nonneg (x8ip (x8vec X) x)
    have hn2 := norm_nonneg (x8ip (x8vec Y) x)
    have := h1 x
    have := h2 x
    nlinarith [sq_nonneg (‖x8ip (x8vec X) x‖ - ‖x8ip (x8vec Y) x‖),
      norm_nonneg (x8ip (x8vec X) x + x8ip (x8vec Y) x)]
  | smul c X _ hX =>
    obtain ⟨C1, hC1, h1⟩ := hX
    refine ⟨‖c‖ ^ 2 * C1, by positivity, fun x => ?_⟩
    have : x8vec (c • X) = c • x8vec X := rfl
    rw [this, x8_ip_smul, norm_mul, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 x) (by positivity)

lemma x8_dom (N G : Superop A B) (hG : IsChannel G)
    (hK : bipartiteGraph G ≤ bipartiteGraph N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (x8Q (choi G) x).re ≤ C * (x8Q (choi N) x).re := by
  obtain ⟨m, E, hE, hGE⟩ := hG
  have hmem : ∀ j, E j ∈ bipartiteGraph N := fun j =>
    hK (Submodule.subset_span ⟨m, E, hE, hGE, j, rfl⟩)
  choose C hC0 hC using fun j => x8_gen_bound N (E j) (hmem j)
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC0 j, fun x => ?_⟩
  rw [x8_Q_choi_re E G hGE, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => hC j x

lemma x8_tr_rank1 (J : Matrix (A × B) (A × B) ℂ) (v : A × B → ℂ) :
    (J * Matrix.vecMulVec v (star v)).trace = x8Q J v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, x8Q,
    Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma x8_tr_psd (N G : Superop A B) (hN : IsChannel N) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, (x8Q (choi G) x).re ≤ C * (x8Q (choi N) x).re)
    (P : Matrix (A × B) (A × B) ℂ) (hP : P.PosSemidef) :
    0 ≤ (choi N * P).trace.re ∧ (choi G * P).trace.re ≤ C * (choi N * P).trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  simp only [Matrix.mul_sum, Matrix.trace_sum, x8_tr_rank1, Complex.re_sum, Finset.mul_sum]
  exact ⟨Finset.sum_nonneg fun k _ => x8_Q_choi_nonneg N hN (v k),
    Finset.sum_le_sum fun k _ => hC (v k)⟩

lemma x8_tr_one (N : Superop A B) (hN : IsChannel N) (ρ : Matrix A A ℂ) (hρ : ρ.trace = 1) :
    (choi N * Matrix.kronecker ρ (1 : Matrix B B ℂ)).trace = 1 := by
  obtain ⟨m, E, hE, hNE⟩ := hN
  rw [x8_choi_kraus E N hNE, Matrix.sum_mul, Matrix.trace_sum, ← hρ]
  have h1 : ∀ a a', ∑ i, ∑ b, conj (E i b a) * E i b a' = if a = a' then 1 else 0 := by
    intro a a'
    have := congrFun (congrFun hE a) a'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, Matrix.one_apply] at this
    exact this
  have h2 : ∀ i, (Matrix.vecMulVec (x8vec (E i)) (star (x8vec (E i))) *
      Matrix.kronecker ρ (1 : Matrix B B ℂ)).trace =
      ∑ a, ∑ a', ρ a' a * ∑ b, conj (E i b a') * E i b a := by
    intro i
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, x8vec, Pi.star_apply,
      RCLike.star_def, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [h2]
  calc ∑ i, ∑ a, ∑ a', ρ a' a * ∑ b, conj (E i b a') * E i b a
      = ∑ a, ∑ a', ρ a' a * ∑ i, ∑ b, conj (E i b a') * E i b a := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ρ.trace := by
        simp only [h1, mul_ite, mul_one, mul_zero]
        simp [Matrix.trace]

lemma x8_eff (N : Superop A B) (hN : IsChannel N) {lam : ℝ} {ρ : Matrix A A ℂ}
    {F : Matrix (A × B) (A × B) ℂ} (hf : SuccessFeasible true lam⁻¹ ρ F) :
    (Matrix.kronecker ρ (1 : Matrix B B ℂ) - F).PosSemidef ∧
    effectProb (choi N) F = 1 - (choi N * (Matrix.kronecker ρ (1 : Matrix B B ℂ) - F)).trace.re := by
  obtain ⟨hρ, -, hle, -, -⟩ := hf
  refine ⟨hle, ?_⟩
  unfold effectProb
  rw [Matrix.mul_sub, Matrix.trace_sub, x8_tr_one N hN ρ hρ.2]
  simp

lemma x8_rs (N G : Superop A B) (hN : IsChannel N) (hG : IsChannel G)
    (hK : bipartiteGraph G ≤ bipartiteGraph N) (lam : ℝ)
    (h : 1 ≤ realSuccess true N lam) : 1 ≤ realSuccess true G lam := by
  obtain ⟨C, hC0, hC⟩ := x8_dom N G hG hK
  have hbd : ∀ (M : Superop A B), IsChannel M → BddAbove (successValues true M lam) := by
    intro M hM
    refine ⟨1, ?_⟩
    rintro s ⟨ρ, F, hf, rfl⟩
    obtain ⟨hP, he⟩ := x8_eff M hM hf
    rw [he]
    linarith [(x8_tr_psd M M hM 1 zero_le_one (fun x => by simp) _ hP).1]
  have hne : (successValues true N lam).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    unfold realSuccess at h
    rw [hc, Real.sSup_empty] at h
    linarith
  unfold realSuccess at h ⊢
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε' : 0 < ε / (C + 1) := by positivity
  obtain ⟨s, ⟨ρ, F, hf, rfl⟩, hs⟩ :=
    exists_lt_of_lt_csSup hne (show 1 - ε / (C + 1) < sSup (successValues true N lam) by linarith)
  have hmem : effectProb (choi G) F ∈ successValues true G lam := ⟨ρ, F, hf, rfl⟩
  have hsup := le_csSup (hbd G hG) hmem
  obtain ⟨hP, heN⟩ := x8_eff N hN hf
  obtain ⟨-, heG⟩ := x8_eff G hG hf
  obtain ⟨hnn, hdom⟩ := x8_tr_psd N G hN C hC0 hC _ hP
  rw [heN] at hs
  rw [heG] at hsup
  have h1 : C * (choi N * (Matrix.kronecker ρ (1 : Matrix B B ℂ) - F)).trace.re ≤
      C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (by linarith) hC0
  have h2 : C * (ε / (C + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  linarith

theorem x8_main [Nonempty A] [Nonempty B] (N G : Superop A B)
    (hN : IsChannel N) (hG : IsChannel G) (hK : bipartiteGraph N = bipartiteGraph G) :
    zeroMessages true N = zeroMessages true G := by
  unfold zeroMessages oneShot
  congr 2
  ext r
  constructor
  · rintro ⟨lam, h1, h2, rfl⟩
    exact ⟨lam, h1, by rw [sub_zero] at h2 ⊢; exact x8_rs N G hN hG hK.ge lam h2, rfl⟩
  · rintro ⟨lam, h1, h2, rfl⟩
    exact ⟨lam, h1, by rw [sub_zero] at h2 ⊢; exact x8_rs G N hG hN hK.le lam h2, rfl⟩

end QAlgorithms.Papers.Independent.Dependency50.P23

end

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P23

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N G : QAlgorithms.Superop A B)
    (hN : QAlgorithms.IsChannel N) (hG : QAlgorithms.IsChannel G)
    (hK : bipartiteGraph N = bipartiteGraph G) :
    zeroMessages true N = zeroMessages true G := x8_main N G hN hG hK

end
