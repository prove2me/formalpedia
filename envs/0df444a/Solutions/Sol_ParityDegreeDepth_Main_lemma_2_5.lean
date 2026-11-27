-- Prove2me | solution 1 for ParityDegreeDepth.Main.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:22:27.394534+00:00
-- url     : https://prove2.me/submissions/1166e4fa-96bd-44b9-b44a-5cb74f682a7d

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

open scoped BigOperators
noncomputable section

namespace P2MFourier

/-- the sign `(-1)^z` of `z ∈ 𝔽₂` -/
def sg (z : ZMod 2) : ℝ := (-1 : ℝ) ^ z.val

lemma sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  unfold sg; rw [ZMod.val_add, ← pow_add, ← neg_one_pow_eq_pow_mod_two]

lemma sg_zero : sg 0 = 1 := by simp [sg]

lemma sg_one : sg 1 = -1 := by unfold sg; simp [ZMod.val_one]

lemma pself {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]; exact CharTwo.add_self_eq_zero (x i)

lemma eq_of_add_eq_zero' {n : ℕ} {x y : Fin n → ZMod 2} (h : y + x = 0) : y = x := by
  calc y = y + (x + x) := by rw [pself, add_zero]
    _ = (y + x) + x := by rw [add_assoc]
    _ = x := by rw [h, zero_add]

lemma zmod2_eq_one (z : ZMod 2) (h : z ≠ 0) : z = 1 := by revert z; decide

lemma sg_mul_self (a : ZMod 2) : sg a * sg a = 1 := by
  rw [← sg_add]; simp [sg_zero, CharTwo.add_self_eq_zero]

lemma abs_sg (a : ZMod 2) : |sg a| = 1 := by
  unfold sg; fin_cases a <;> norm_num [ZMod.val]

variable {n : ℕ}

lemma dot_add_right (ξ x y : Fin n → ZMod 2) : ξ ⬝ᵥ (x + y) = ξ ⬝ᵥ x + ξ ⬝ᵥ y := by
  simp [dotProduct_add]

lemma dot_add_left (ξ η x : Fin n → ZMod 2) : (ξ + η) ⬝ᵥ x = ξ ⬝ᵥ x + η ⬝ᵥ x := by
  simp [add_dotProduct]

/-- character sum -/
lemma sum_sg_dot (ξ : Fin n → ZMod 2) :
    ∑ x : Fin n → ZMod 2, sg (ξ ⬝ᵥ x) = if ξ = 0 then (2 : ℝ) ^ n else 0 := by
  split_ifs with h
  · subst h; simp [sg_zero, Finset.card_univ, ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
      by_contra hc; push Not at hc; exact h (funext hc)
    have hi1 : ξ i = 1 := zmod2_eq_one _ hi
    have key : ∀ x : Fin n → ZMod 2, sg (ξ ⬝ᵥ (x + Pi.single i 1)) = - sg (ξ ⬝ᵥ x) := by
      intro x
      rw [dot_add_right, sg_add, dotProduct_single, mul_one, hi1, sg_one, mul_neg_one]
    have hS : ∑ x : Fin n → ZMod 2, sg (ξ ⬝ᵥ x) = ∑ x : Fin n → ZMod 2, - sg (ξ ⬝ᵥ x) := by
      rw [← Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2))) (fun x => sg (ξ ⬝ᵥ x))]
      exact Finset.sum_congr rfl fun x _ => key x
    rw [Finset.sum_neg_distrib] at hS
    linarith

lemma boolFourier_eq (f : (Fin n → ZMod 2) → ℝ) (ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier f ξ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * sg (ξ ⬝ᵥ x) := by
  rw [QAlgorithms.boolFourier]; rfl

lemma two_pow_ne : ((2 : ℝ) ^ n) ≠ 0 := by positivity

/-- Fourier inversion -/
lemma fourier_inversion (f : (Fin n → ZMod 2) → ℝ) (x : Fin n → ZMod 2) :
    f x = ∑ ξ, QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ x) := by
  simp only [boolFourier_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ y : Fin n → ZMod 2, ∑ ξ : Fin n → ZMod 2, ((2:ℝ) ^ n)⁻¹ * (f y * sg (ξ ⬝ᵥ y)) *
      sg (ξ ⬝ᵥ x) = if y = x then f x else 0 := by
    intro y
    have h2 : ∀ ξ : Fin n → ZMod 2, ((2:ℝ) ^ n)⁻¹ * (f y * sg (ξ ⬝ᵥ y)) * sg (ξ ⬝ᵥ x) =
        ((2:ℝ) ^ n)⁻¹ * f y * sg ((y + x) ⬝ᵥ ξ) := by
      intro ξ
      rw [dot_add_left, sg_add, dotProduct_comm y, dotProduct_comm x]; ring
    simp only [h2, ← Finset.mul_sum, sum_sg_dot]
    by_cases hyx : y = x
    · subst hyx; simp [pself]; field_simp
    · have : y + x ≠ 0 := by
        intro h; apply hyx; exact eq_of_add_eq_zero' h
      simp [this, hyx]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- product formula -/
lemma fourier_mul (f g : (Fin n → ZMod 2) → ℝ) (ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun x => f x * g x) ξ =
      ∑ η, QAlgorithms.boolFourier f η * QAlgorithms.boolFourier g (ξ + η) := by
  conv_lhs => rw [boolFourier_eq]
  conv_lhs =>
    enter [2, 2, x]
    rw [fourier_inversion f x]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [boolFourier_eq g (ξ + η), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dot_add_left, sg_add]
  ring

def l1 (f : (Fin n → ZMod 2) → ℝ) : ℝ := ∑ a, |QAlgorithms.boolFourier f a|

lemma l1_nonneg (f : (Fin n → ZMod 2) → ℝ) : 0 ≤ l1 f :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1_mul_le (f g : (Fin n → ZMod 2) → ℝ) : l1 (fun x => f x * g x) ≤ l1 f * l1 g := by
  unfold l1
  simp only [fourier_mul]
  calc ∑ ξ, |∑ η, QAlgorithms.boolFourier f η * QAlgorithms.boolFourier g (ξ + η)|
      ≤ ∑ ξ, ∑ η, |QAlgorithms.boolFourier f η| * |QAlgorithms.boolFourier g (ξ + η)| := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp [abs_mul]
    _ = ∑ η, |QAlgorithms.boolFourier f η| * ∑ ξ, |QAlgorithms.boolFourier g (ξ + η)| := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ = ∑ η, |QAlgorithms.boolFourier f η| * ∑ ξ, |QAlgorithms.boolFourier g ξ| := by
        refine Finset.sum_congr rfl fun η _ => ?_
        congr 1
        exact Equiv.sum_comp (Equiv.addRight η) (fun ξ => |QAlgorithms.boolFourier g ξ|)
    _ = _ := by rw [Finset.sum_mul]

lemma fourier_translate (f : (Fin n → ZMod 2) → ℝ) (a ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun x => f (x + a)) ξ = sg (ξ ⬝ᵥ a) * QAlgorithms.boolFourier f ξ := by
  rw [boolFourier_eq, boolFourier_eq]
  have hre : ∑ x, f x * sg (ξ ⬝ᵥ x) = ∑ x, f (x + a) * sg (ξ ⬝ᵥ (x + a)) :=
    (Equiv.sum_comp (Equiv.addRight a) (fun x => f x * sg (ξ ⬝ᵥ x))).symm
  rw [hre, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dot_add_right, sg_add]
  have := sg_mul_self (ξ ⬝ᵥ a)
  calc ((2:ℝ) ^ n)⁻¹ * (f (x + a) * sg (ξ ⬝ᵥ x))
      = ((2:ℝ) ^ n)⁻¹ * (f (x + a) * sg (ξ ⬝ᵥ x)) * (sg (ξ ⬝ᵥ a) * sg (ξ ⬝ᵥ a)) := by
        rw [this, mul_one]
    _ = _ := by ring

lemma l1_translate (f : (Fin n → ZMod 2) → ℝ) (a : Fin n → ZMod 2) :
    l1 (fun x => f (x + a)) = l1 f := by
  unfold l1; simp [fourier_translate, abs_mul, abs_sg]

lemma fourier_mul_char (f : (Fin n → ZMod 2) → ℝ) (a ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun x => f x * sg (a ⬝ᵥ x)) ξ =
      QAlgorithms.boolFourier f (ξ + a) := by
  rw [boolFourier_eq, boolFourier_eq]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dot_add_left, sg_add]; ring

lemma l1_mul_char (f : (Fin n → ZMod 2) → ℝ) (a : Fin n → ZMod 2) :
    l1 (fun x => f x * sg (a ⬝ᵥ x)) = l1 f := by
  unfold l1; simp only [fourier_mul_char]
  exact Equiv.sum_comp (Equiv.addRight a) (fun ξ => |QAlgorithms.boolFourier f ξ|)

end P2MFourier

end

namespace ParityDegreeDepth.Main


private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def phase {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (p x).val

private def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|

private def signDerivatives {n k : ℕ} (f : Vec n (ZMod 2) → ℝ)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ℝ :=
  (List.ofFn h).foldl (fun g v x => g x * g (x + v)) f



end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- lemma 2 5; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (h : Fin k → Vec n (ZMod 2)) :
    spectralNorm (signDerivatives (phase p) h) ≤ spectralNorm (phase p) ^ (2 ^ k) := by
  have key : ∀ (k : ℕ) (f : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
      P2MFourier.l1 ((List.ofFn h).foldl (fun g v x => g x * g (x + v)) f) ≤
        P2MFourier.l1 f ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => intro f h; simp
    | succ k ih =>
      intro f h
      rw [List.ofFn_succ, List.foldl_cons]
      refine (ih _ (fun i => h i.succ)).trans ?_
      have h1 : P2MFourier.l1 (fun x => f x * f (x + h 0)) ≤ P2MFourier.l1 f ^ 2 := by
        refine (P2MFourier.l1_mul_le _ _).trans ?_
        rw [P2MFourier.l1_translate f (h 0), sq]
      calc P2MFourier.l1 (fun x => f x * f (x + h 0)) ^ 2 ^ k
          ≤ (P2MFourier.l1 f ^ 2) ^ 2 ^ k := pow_le_pow_left₀ (P2MFourier.l1_nonneg _) h1 _
        _ = P2MFourier.l1 f ^ 2 ^ (k + 1) := by rw [← pow_mul, pow_succ, mul_comm]
  exact key k (phase p) h



