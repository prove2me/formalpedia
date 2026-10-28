-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.depolarizingAntidegraderNonunique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:01:25.627796+00:00
-- url     : https://prove2.me/submissions/b3c7eb3e-f6fb-4d6f-9f3d-333afd2c6221

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

theorem S174C_comp {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (V : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) (e e' : E) :
    complementaryChannel V rho e e' = ∑ b, ∑ a, ∑ a', V (b,e) a * rho a a' * conj (V (b,e') a') := by
  simp only [complementaryChannel, QAlgorithms.traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]; rfl

theorem S174C_kraus {K A B : Type} [Fintype K] [Fintype A]
    (L : K → Matrix B A ℂ) (sig : Matrix A A ℂ) (b b' : B) :
    krausApply L sig b b' = ∑ k, ∑ e, ∑ e', L k b e * sig e e' * conj (L k b' e') := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]; rfl

theorem S174C_chan {K ι κ : Type} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (h : ∑ j, (E j)ᴴ * E j = 1) : IsChannel (krausApply E) := by
  refine ⟨Fintype.card K, fun j => E ((Fintype.equivFin K).symm j), ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [← h]; exact Equiv.sum_comp (Fintype.equivFin K).symm (fun j => (E j)ᴴ * E j)
  · unfold krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K).symm (fun j => E j * rho * (E j)ᴴ)).symm

def S174C_u (x : ℝ) : Fin 4 → Fin 4 → ℝ := ![![1,x,x,x], ![0,1,1,1], ![0,1,-1,0], ![0,1,1,-2]]
def S174C_w (x y : ℝ) : Fin 4 → ℝ := ![1, (1+2*y)/3 - x^2, (1-y)/2, (1-y)/6]
def S174C_s (x y : ℝ) (t : Fin 4) : ℂ := ((Real.sqrt (S174C_w x y t / 2) : ℝ) : ℂ)
def S174C_Kg (s : Fin 4 → ℂ) (u : Fin 4 → Fin 4 → ℂ) (P : Fin 4 → Matrix Bool Bool ℂ) :
    Fin 4 × Bool → Matrix Bool (Fin 4) ℂ :=
  fun tc b k => s tc.1 * u tc.1 k * P k b tc.2
def S174C_K (x y : ℝ) : Fin 4 × Bool → Matrix Bool (Fin 4) ℂ :=
  S174C_Kg (S174C_s x y) (fun t k => (S174C_u x t k : ℂ)) paulis
def S174C_F (x y : ℝ) : Fin 4 → Fin 4 → ℝ := ![![1,x,x,x], ![x,1,y,y], ![x,y,1,y], ![x,y,y,1]]

theorem S174C_L1 (s : Fin 4 → ℂ) (u : Fin 4 → Fin 4 → ℂ) (P : Fin 4 → Matrix Bool Bool ℂ)
    (r : Matrix (Fin 4) (Fin 4) ℂ) (b b' : Bool) :
    krausApply (S174C_Kg s u P) r b b' =
    ∑ k, ∑ l, r k l * (∑ t, s t * conj (s t) * u t k * conj (u t l)) * ∑ c, P k b c * conj (P l b' c) := by
  rw [S174C_kraus]
  simp only [S174C_Kg, Fintype.sum_prod_type, Fin.sum_univ_four, Fintype.sum_bool, map_mul]
  ring

theorem S174C_L1' (s : Fin 4 → ℂ) (u : Fin 4 → Fin 4 → ℂ) (P : Fin 4 → Matrix Bool Bool ℂ) (k l : Fin 4) :
    (∑ tc, (S174C_Kg s u P tc)ᴴ * S174C_Kg s u P tc) k l =
    (∑ t, s t * conj (s t) * u t l * conj (u t k)) * ∑ b, ∑ c, P l b c * conj (P k b c) := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, S174C_Kg]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_four, Fintype.sum_bool, map_mul, RCLike.star_def]
  ring

theorem S174C_L2 (x y : ℝ) (h2 : 0 ≤ (1+2*y)/3 - x^2) (h3 : 0 ≤ 1 - y) (k l : Fin 4) :
    (∑ t, S174C_s x y t * conj (S174C_s x y t) * (S174C_u x t k : ℂ) * conj (S174C_u x t l : ℂ)) =
      (S174C_F x y k l : ℂ) / 2 := by
  have hs : ∀ t, S174C_s x y t * conj (S174C_s x y t) = ((S174C_w x y t / 2 : ℝ) : ℂ) := by
    intro t
    have : 0 ≤ S174C_w x y t / 2 := by
      fin_cases t <;> simp [S174C_w] <;> linarith
    rw [S174C_s, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt this]
  simp only [hs, Complex.conj_ofReal]
  fin_cases k <;> fin_cases l <;> simp [S174C_u, S174C_w, S174C_F, Fin.sum_univ_four] <;> ring

theorem S174C_formula (x y : ℝ) (h2 : 0 ≤ (1+2*y)/3 - x^2) (h3 : 0 ≤ 1 - y)
    (r : Matrix (Fin 4) (Fin 4) ℂ) (b b' : Bool) :
    krausApply (S174C_K x y) r b b' =
    ∑ k, ∑ l, r k l * ((S174C_F x y k l : ℂ) / 2) * ∑ c, paulis k b c * conj (paulis l b' c) := by
  have := S174C_L1 (S174C_s x y) (fun t k => (S174C_u x t k : ℂ)) paulis r b b'
  simp only [S174C_L2 x y h2 h3] at this
  exact this

theorem S174C_isChan (x y : ℝ) (h2 : 0 ≤ (1+2*y)/3 - x^2) (h3 : 0 ≤ 1 - y) :
    IsChannel (krausApply (S174C_K x y)) := by
  apply S174C_chan
  ext k l
  have := S174C_L1' (S174C_s x y) (fun t k => (S174C_u x t k : ℂ)) paulis k l
  simp only [S174C_L2 x y h2 h3] at this
  refine this.trans ?_
  fin_cases k <;> fin_cases l <;>
    simp [S174C_F, paulis, pauliX, pauliY, pauliZ, Fintype.sum_bool, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

theorem S174C_anti (a0 b x y : ℝ) (h : 2*a0*b*x + 2*b^2*y = a0^2 - b^2)
    (rho : Matrix Bool Bool ℂ) (i j : Bool) :
    ∑ k, ∑ l, complementaryChannel (indexedKrausDilation (pauliKraus ![a0,b,b,b])) rho k l *
      ((S174C_F x y k l : ℂ) / 2) * ∑ c, paulis k i c * conj (paulis l j c) =
    qubitPauliMap ![a0,b,b,b] rho i j := by
  have hc : ((2*a0*b*x + 2*b^2*y : ℝ) : ℂ) = ((a0^2 - b^2 : ℝ) : ℂ) := by rw [h]
  push_cast at hc
  simp only [S174C_comp, qubitPauliMap, S174C_kraus]
  cases i <;> cases j <;>
    simp [indexedKrausDilation, pauliKraus, S174C_F, paulis, pauliX, pauliY, pauliZ, Fintype.sum_bool,
      Fin.sum_univ_four] <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  · linear_combination (rho false false - rho true true)/2 * hc
  · linear_combination rho false true * hc
  · linear_combination rho true false * hc
  · linear_combination (rho true true - rho false false)/2 * hc

theorem S174C_good (lam a0 b z : ℝ) (hp : 0 < 1 + 3*lam) (hq : 0 < 1 - lam)
    (ha0 : a0^2 = (1+3*lam)/4) (hb : b^2 = (1-lam)/4) (ha0p : 0 < a0) (hbp : 0 < b)
    (hz1 : 0 ≤ (1+3*lam)*((1+3*lam) - 4*z) - 12*z^2) (hz2 : ((1+3*lam) - 2)/2 ≤ z) :
    let x := z/(2*a0*b)
    let y := (lam - z)/(2*b^2)
    0 ≤ (1+2*y)/3 - x^2 ∧ 0 ≤ 1 - y ∧ 2*a0*b*x + 2*b^2*y = a0^2 - b^2 := by
  intro x y
  have hab : 0 < a0*b := mul_pos ha0p hbp
  have hx : x * (2*a0*b) = z := by simp only [x]; field_simp
  have hy : y * (2*b^2) = lam - z := by simp only [y]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have key : ((1+2*y)/3 - x^2) * (12*(a0*b)^2) = ((1+3*lam)*((1+3*lam) - 4*z) - 12*z^2)/4 := by
      have e1 : x^2 * (12*(a0*b)^2) = 3*z^2 := by rw [← hx]; ring
      have e2 : (1+2*y) * (4*(a0*b)^2) = (1+3*lam)*((1+3*lam) - 4*z)/4 := by
        have : (1+2*y) * (4*(a0*b)^2) = 4*a0^2*b^2 + 4*a0^2*(y*(2*b^2)) := by ring
        rw [this, hy, ha0, hb]; ring
      linear_combination e2 - e1
    have hpos : 0 < 12*(a0*b)^2 := by positivity
    by_contra hc
    push Not at hc
    have := mul_neg_of_neg_of_pos hc hpos
    rw [key] at this
    linarith
  · have : y * (2*b^2) ≤ 1 * (2*b^2) := by rw [hy, hb]; linarith
    have := le_of_mul_le_mul_right this (by positivity)
    linarith
  · have : 2*a0*b*x = z := by linarith [hx]
    rw [this, show 2*b^2*y = y*(2*b^2) by ring, hy, ha0, hb]; ring

theorem S174C_main (lam a0 b z : ℝ) (hp : 0 < 1 + 3*lam) (hq : 0 < 1 - lam)
    (ha0 : a0^2 = (1+3*lam)/4) (hb : b^2 = (1-lam)/4) (ha0p : 0 < a0) (hbp : 0 < b)
    (hz1 : 0 ≤ (1+3*lam)*((1+3*lam) - 4*z) - 12*z^2) (hz2 : ((1+3*lam) - 2)/2 ≤ z) :
    IsChannel (krausApply (S174C_K (z/(2*a0*b)) ((lam - z)/(2*b^2)))) ∧
    (∀ rho, krausApply (S174C_K (z/(2*a0*b)) ((lam - z)/(2*b^2)))
      (complementaryChannel (indexedKrausDilation (pauliKraus ![a0,b,b,b])) rho) = qubitPauliMap ![a0,b,b,b] rho) ∧
    krausApply (S174C_K (z/(2*a0*b)) ((lam - z)/(2*b^2))) (Matrix.single 0 1 1) false true
      = (((z/(2*a0*b) : ℝ) : ℂ))/2 := by
  obtain ⟨h2, h3, h⟩ := S174C_good lam a0 b z hp hq ha0 hb ha0p hbp hz1 hz2
  refine ⟨S174C_isChan _ _ h2 h3, fun rho => ?_, ?_⟩
  · ext i j
    rw [S174C_formula _ _ h2 h3]
    exact S174C_anti _ _ _ _ h rho i j
  · rw [S174C_formula _ _ h2 h3]
    simp [Fin.sum_univ_four, Matrix.single_apply, S174C_F, paulis, pauliX, Fintype.sum_bool]


theorem solution (lam : ℝ)
    (hlo : -1/3 < lam) (hhi : lam < 2/3) :
    let a := depolarizingAmplitudes lam
    let U := indexedKrausDilation (pauliKraus a)
    ∃ D1 D2 : Superop (Fin 4) Bool, IsChannel D1 ∧ IsChannel D2 ∧ D1 ≠ D2 ∧
      (∀ rho, D1 (complementaryChannel U rho) = qubitPauliMap a rho) ∧
      (∀ rho, D2 (complementaryChannel U rho) = qubitPauliMap a rho) := by
  intro a U
  have hp : 0 < 1 + 3*lam := by linarith
  have hq : 0 < 1 - lam := by linarith
  have ha : a = ![Real.sqrt ((1+3*lam)/4), Real.sqrt ((1-lam)/4), Real.sqrt ((1-lam)/4), Real.sqrt ((1-lam)/4)] := rfl
  have ha0 : (Real.sqrt ((1+3*lam)/4))^2 = (1+3*lam)/4 := Real.sq_sqrt (by linarith)
  have hb : (Real.sqrt ((1-lam)/4))^2 = (1-lam)/4 := Real.sq_sqrt (by linarith)
  have ha0p : 0 < Real.sqrt ((1+3*lam)/4) := Real.sqrt_pos.mpr (by linarith)
  have hbp : 0 < Real.sqrt ((1-lam)/4) := Real.sqrt_pos.mpr (by linarith)
  have hU : U = indexedKrausDilation (pauliKraus a) := rfl
  rw [hU, ha]
  set a0 := Real.sqrt ((1+3*lam)/4)
  set b := Real.sqrt ((1-lam)/4)
  set p := 1 + 3*lam with hpdef
  have hp3 : p < 3 := by linarith
  obtain ⟨c1, e1, v1⟩ := S174C_main lam a0 b (p/6) hp hq ha0 hb ha0p hbp
    (by nlinarith) (by nlinarith)
  obtain ⟨c2, e2, v2⟩ := S174C_main lam a0 b (p/6 - p*(3-p)/9) hp hq ha0 hb ha0p hbp
    (by nlinarith [mul_pos hp (sub_pos.mpr hp3), mul_pos (mul_pos hp (sub_pos.mpr hp3)) hp])
    (by nlinarith [sq_nonneg (p-3)])
  refine ⟨_, _, c1, c2, ?_, e1, e2⟩
  intro hD
  have := congrFun hD (Matrix.single 0 1 1)
  have := congrFun (congrFun this false) true
  rw [v1, v2] at this
  have hne : p/6 ≠ p/6 - p*(3-p)/9 := by
    have : 0 < p*(3-p)/9 := by have := mul_pos hp (sub_pos.mpr hp3); linarith
    linarith
  apply hne
  have hab : 0 < 2*a0*b := by positivity
  have h'' : (((p/6)/(2*a0*b) : ℝ) : ℂ) = (((p/6 - p*(3-p)/9)/(2*a0*b) : ℝ) : ℂ) := by
    linear_combination 2 * this
  have h' := Complex.ofReal_injective h''
  field_simp at h'
  linarith

end
