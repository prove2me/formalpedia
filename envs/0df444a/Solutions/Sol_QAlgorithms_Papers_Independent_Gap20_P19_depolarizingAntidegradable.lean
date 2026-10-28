-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.depolarizingAntidegradable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:48:52.086992+00:00
-- url     : https://prove2.me/submissions/acb61b10-5fd2-4f4f-a82c-f284bbb7d349

import Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_antidegradableConvex
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Gap20 QAlgorithms.Papers.Independent.Gap20.P19
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker
open Filter Topology
open QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Claimed50.P48
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

theorem S174A_formula (l : ℝ) (rho : Matrix Bool Bool ℂ) :
    multiplierChannel ![l,l,l] rho = (l:ℂ) • rho + (((1-l)/2 : ℂ) * rho.trace) • (1 : Matrix Bool Bool ℂ) := by
  ext i j
  cases i <;> cases j <;>
    simp [multiplierChannel, QubitChannels.blochAffineMap, QubitChannels.sigma, pauliX, pauliY, pauliZ,
      Fin.sum_univ_three, Matrix.diagonal, Matrix.trace, Matrix.mul_apply, Fintype.sum_bool] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

theorem S174A_chan {K ι κ : Type} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (h : ∑ j, (E j)ᴴ * E j = 1) : IsChannel (krausApply E) := by
  refine ⟨Fintype.card K, fun j => E ((Fintype.equivFin K).symm j), ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [← h]; exact Equiv.sum_comp (Fintype.equivFin K).symm (fun j => (E j)ᴴ * E j)
  · unfold krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K).symm (fun j => E j * rho * (E j)ᴴ)).symm

theorem S174A_lower (l : ℝ) (hPhi : IsChannel (multiplierChannel ![l,l,l])) : -1/3 ≤ l := by
  obtain ⟨m, E, -, hE⟩ := hPhi
  have key : ∀ a c : Bool, multiplierChannel ![l,l,l] (Matrix.single a c 1) a c
      = ∑ j, E j a a * conj (E j c c) := by
    intro a c
    rw [hE]
    simp [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, Fintype.sum_bool]
    cases a <;> cases c <;> simp
  have hsum : ((1 + 3*l : ℝ) : ℂ) = ∑ j, (E j false false + E j true true) * conj (E j false false + E j true true) := by
    have h1 := key false false
    have h2 := key false true
    have h3 := key true false
    have h4 := key true true
    simp only [S174A_formula] at h1 h2 h3 h4
    simp [Matrix.trace, Fintype.sum_bool, Matrix.single_apply] at h1 h2 h3 h4
    simp only [map_add, add_mul, mul_add, Finset.sum_add_distrib]
    rw [← h1, ← h2, ← h3, ← h4]; push_cast; ring
  have hnn : (0:ℂ) ≤ ((1 + 3*l : ℝ) : ℂ) := by
    rw [hsum]
    apply Finset.sum_nonneg
    intro j _
    rw [Complex.mul_conj]
    exact_mod_cast Complex.normSq_nonneg _
  have := Complex.zero_le_real.mp hnn
  linarith

theorem S174A_recv {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (V : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    receiverChannel V rho b b' = ∑ e, ∑ a, ∑ a', V (b,e) a * rho a a' * conj (V (b',e) a') := by
  simp only [receiverChannel, traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]; rfl

theorem S174A_comp {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (V : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) (e e' : E) :
    complementaryChannel V rho e e' = ∑ b, ∑ a, ∑ a', V (b,e) a * rho a a' * conj (V (b,e') a') := by
  simp only [complementaryChannel, QAlgorithms.traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]; rfl

theorem S174A_kraus {K A B : Type} [Fintype K] [Fintype A]
    (L : K → Matrix B A ℂ) (sig : Matrix A A ℂ) (b b' : B) :
    krausApply L sig b b' = ∑ k, ∑ e, ∑ e', L k b e * sig e e' * conj (L k b' e') := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]; rfl

theorem S174A_iso {A B E : Type} [Fintype A] [Fintype B] [Fintype E] [DecidableEq A]
    (V : Matrix (B × E) A ℂ) (h : ∀ a a', ∑ b, ∑ e, conj (V (b,e) a) * V (b,e) a' = if a = a' then 1 else 0) :
    IsIsometry V := by
  unfold IsIsometry
  ext a a'
  rw [Matrix.mul_apply, Matrix.one_apply, ← h, ← Finset.sum_product']
  rfl

theorem S174A_s6 : ((Real.sqrt 6 : ℝ) : ℂ) ^ 2 = 6 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl

def S174A_enc (b a : Bool) : Fin 4 := if b then (if a then 3 else 2) else (if a then 1 else 0)

def S174A_cV : Matrix (Bool × Fin 4) Bool ℂ := fun p a =>
  let al : ℂ := ((Real.sqrt 6 : ℝ) : ℂ) / 3
  if a then (if p = (true,3) then al else if p = (false,2) ∨ p = (true,0) then al/2 else 0)
  else (if p = (false,0) then al else if p = (false,3) ∨ p = (true,1) then al/2 else 0)

def S174A_cK : Bool → Matrix Bool (Fin 4) ℂ := fun a b e => if e = S174A_enc b a then 1 else 0

theorem S174A_cloner : ∃ envSize : ℕ, ∃ witness : Matrix (Bool × Fin envSize) Bool ℂ,
    receiverChannel witness = multiplierChannel ![2/3,2/3,2/3] ∧ IsAntidegradable witness := by
  have hR : receiverChannel S174A_cV = multiplierChannel ![2/3,2/3,2/3] := by
    funext rho; ext b b'
    rw [S174A_recv, S174A_formula]
    cases b <;> cases b' <;>
      simp [S174A_cV, Fintype.sum_prod_type, Fin.sum_univ_four, Fintype.sum_bool, Matrix.trace, map_ofNat] <;>
      ring_nf <;> rw [S174A_s6] <;> ring
  refine ⟨4, S174A_cV, hR, ?_, krausApply S174A_cK, S174A_chan _ ?_, fun rho => ?_⟩
  · apply S174A_iso
    intro a a'
    cases a <;> cases a' <;>
      simp [S174A_cV, Fintype.sum_prod_type, Fin.sum_univ_four, Fintype.sum_bool, map_ofNat] <;>
      ring_nf <;> rw [S174A_s6] <;> ring
  · ext e e'
    fin_cases e <;> fin_cases e' <;>
      simp [S174A_cK, S174A_enc, Matrix.mul_apply, Fintype.sum_bool]
  · ext b b'
    rw [S174A_recv, S174A_kraus]
    simp only [S174A_comp]
    cases b <;> cases b' <;>
      simp [S174A_cV, S174A_cK, S174A_enc, Fintype.sum_prod_type, Fin.sum_univ_four, Fintype.sum_bool] <;>
      ring_nf

theorem S174A_s3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl

def S174A_u (k : Fin 6) (a : Bool) : ℂ :=
  if a then ![0,1,1,-1,Complex.I,-Complex.I] k else ![1,0,1,1,1,1] k

def S174A_ub (k : Fin 6) (a : Bool) : ℂ := S174A_u (![1,0,3,2,5,4] k) a

def S174A_g (k : Fin 6) : ℂ := ![1,1,1/2,1/2,1/2,1/2] k

def S174A_oV : Matrix (Bool × Fin 6) Bool ℂ := fun p a =>
  ((Real.sqrt 3 : ℝ) : ℂ) / 3 * S174A_g p.2 * S174A_ub p.2 p.1 * conj (S174A_u p.2 a)

def S174A_oK : Fin 6 × Bool → Matrix Bool (Fin 6) ℂ := fun km b j =>
  if j = km.1 then S174A_g km.1 * S174A_ub km.1 b * conj (S174A_ub km.1 km.2) else 0

theorem S174A_oKk (j : Fin 6) : ∑ m : Bool, ∑ b : Bool,
    star (S174A_g j * S174A_ub j b * conj (S174A_ub j m)) * (S174A_g j * S174A_ub j b * conj (S174A_ub j m)) = 1 := by
  fin_cases j <;> simp [S174A_g, S174A_u, S174A_ub, Fintype.sum_bool, map_ofNat] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring_nf

theorem S174A_oD (sig : Matrix (Fin 6) (Fin 6) ℂ) (b b' : Bool) :
    krausApply S174A_oK sig b b' = ∑ k, sig k k * ∑ m : Bool,
      (S174A_g k * S174A_ub k b * conj (S174A_ub k m)) * conj (S174A_g k * S174A_ub k b' * conj (S174A_ub k m)) := by
  rw [S174A_kraus, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [S174A_oK, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, apply_ite, map_zero,
    mul_zero, Finset.sum_ite_eq]
  ring

theorem S174A_fact (c g : ℂ) (x y : Bool → ℂ) (rho : Matrix Bool Bool ℂ) (b b' : Bool)
    (h : g * conj g * (∑ m, x m * conj (x m)) * (∑ m, x m * conj (x m)) = 1) :
    ∑ a, ∑ a', (c * g * x b * conj (y a)) * rho a a' * conj (c * g * x b' * conj (y a')) =
    (∑ b'', ∑ a, ∑ a', (c * g * x b'' * conj (y a)) * rho a a' * conj (c * g * x b'' * conj (y a'))) *
      ∑ m, (g * x b * conj (x m)) * conj (g * x b' * conj (x m)) := by
  simp only [Fintype.sum_bool, map_mul, Complex.conj_conj] at h ⊢
  linear_combination (-(c * conj c * g * conj g * x b * conj (x b') *
    (conj (y false) * rho false false * y false + conj (y false) * rho false true * y true +
     conj (y true) * rho true false * y false + conj (y true) * rho true true * y true))) * h

theorem S174A_norm (k : Fin 6) : S174A_g k * conj (S174A_g k) *
    (∑ m, S174A_ub k m * conj (S174A_ub k m)) * (∑ m, S174A_ub k m * conj (S174A_ub k m)) = 1 := by
  fin_cases k <;> simp [S174A_g, S174A_u, S174A_ub, Fintype.sum_bool, map_ofNat] <;> norm_num

theorem S174A_octa : ∃ envSize : ℕ, ∃ witness : Matrix (Bool × Fin envSize) Bool ℂ,
    receiverChannel witness = multiplierChannel ![-1/3,-1/3,-1/3] ∧ IsAntidegradable witness := by
  have hR : receiverChannel S174A_oV = multiplierChannel ![-1/3,-1/3,-1/3] := by
    funext rho; ext b b'
    rw [S174A_recv, S174A_formula]
    cases b <;> cases b' <;>
      simp [S174A_oV, S174A_g, S174A_u, S174A_ub, Fin.sum_univ_succ, Fintype.sum_bool, Matrix.trace, map_ofNat] <;>
      ring_nf <;> rw [S174A_s3] <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  refine ⟨6, S174A_oV, hR, ?_, krausApply S174A_oK, S174A_chan _ ?_, fun rho => ?_⟩
  · apply S174A_iso
    intro a a'
    cases a <;> cases a' <;>
      simp [S174A_oV, S174A_g, S174A_u, S174A_ub, Fin.sum_univ_succ, Fintype.sum_bool, map_ofNat] <;>
      ring_nf <;> rw [S174A_s3] <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  · ext e e'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_prod_type, S174A_oK]
    by_cases h : e = e'
    · subst h
      rw [Finset.sum_eq_single e]
      · simp only [if_true]; exact S174A_oKk e
      · intro k _ hk
        apply Finset.sum_eq_zero; intro m _
        apply Finset.sum_eq_zero; intro b _
        simp [Ne.symm hk]
      · simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro m _
      apply Finset.sum_eq_zero; intro b _
      split_ifs <;> simp_all
  · ext b b'
    rw [S174A_recv, S174A_oD]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [S174A_comp]
    simp only [S174A_oV]
    exact S174A_fact _ _ _ _ _ _ _ (S174A_norm k)

theorem solution (lam : ℝ)
    (hPhi : IsChannel (multiplierChannel ![lam,lam,lam])) (hlam : |lam| ≤ 2/3) :
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (multiplierChannel ![lam,lam,lam]) ∧ IsAntidegradable witness) := by
  have h1 := S174A_lower lam hPhi
  have h2 : lam ≤ 2/3 := (abs_le.mp hlam).2
  obtain ⟨n, W, hW, hA⟩ := antidegradableConvex _ _ S174A_cloner S174A_octa (lam + 1/3)
    (by linarith) (by linarith)
  refine ⟨n, W, ?_, hA⟩
  rw [hW]
  funext rho
  rw [S174A_formula, S174A_formula, S174A_formula]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

end
