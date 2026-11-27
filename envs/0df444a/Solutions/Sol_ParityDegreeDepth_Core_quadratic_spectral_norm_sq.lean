-- Prove2me | solution 1 for ParityDegreeDepth.Core.quadratic_spectral_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:59:55.247315+00:00
-- url     : https://prove2.me/submissions/30c1a5a7-f7e5-4497-85ec-15d19c6dd6a8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityDegreeDepth_Core_tensorEval

-- ===== Four =====

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

-- ===== Four2 =====

open scoped BigOperators
open Matrix
noncomputable section

namespace P2MFourier

variable {n : ℕ}

lemma parseval (f : (Fin n → ZMod 2) → ℝ) :
    ∑ ξ, QAlgorithms.boolFourier f ξ ^ 2 = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x ^ 2 := by
  calc ∑ ξ, QAlgorithms.boolFourier f ξ ^ 2
      = ∑ ξ, QAlgorithms.boolFourier f ξ * (((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * sg (ξ ⬝ᵥ x)) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [sq]; congr 1
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * ∑ ξ, QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ x) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ξ _ => ?_
        ring
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← fourier_inversion f x, sq]

lemma fourier_char (η ζ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun y => sg (η ⬝ᵥ y)) ζ = if η = ζ then 1 else 0 := by
  rw [boolFourier_eq]
  have : ∀ y : Fin n → ZMod 2, sg (η ⬝ᵥ y) * sg (ζ ⬝ᵥ y) = sg ((η + ζ) ⬝ᵥ y) := by
    intro y; rw [dot_add_left, sg_add]
  simp only [this, sum_sg_dot]
  by_cases h : η = ζ
  · subst h; simp [pself]
  · have : η + ζ ≠ 0 := fun h' => h (eq_of_add_eq_zero' h')
    simp [this, h]

lemma fourier_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin n → ZMod 2) → ℝ) (ζ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun y => ∑ i ∈ s, g i y) ζ = ∑ i ∈ s, QAlgorithms.boolFourier (g i) ζ := by
  simp only [boolFourier_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma fourier_const_mul (c : ℝ) (g : (Fin n → ZMod 2) → ℝ) (ζ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (fun y => c * g y) ζ = c * QAlgorithms.boolFourier g ζ := by
  simp only [boolFourier_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => by ring

/-- restriction to an affine subspace (image of an affine map) does not increase the spectral norm -/
theorem l1_affine {m : ℕ} (f : (Fin n → ZMod 2) → ℝ)
    (B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    l1 (fun y => f (a + B y)) ≤ l1 f := by
  classical
  let Bt : (Fin n → ZMod 2) → (Fin m → ZMod 2) := fun ξ => ξ ᵥ* LinearMap.toMatrix' B
  have hBt : ∀ ξ y, ξ ⬝ᵥ B y = Bt ξ ⬝ᵥ y := by
    intro ξ y
    rw [← LinearMap.toMatrix'_mulVec B y, Matrix.dotProduct_mulVec]
  have hexp : (fun y => f (a + B y)) = fun y => ∑ ξ, (QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ a)) *
      sg (Bt ξ ⬝ᵥ y) := by
    funext y
    rw [fourier_inversion f (a + B y)]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [dot_add_right, sg_add, hBt]; ring
  have hF : ∀ ζ, QAlgorithms.boolFourier (fun y => f (a + B y)) ζ =
      ∑ ξ, (QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ a)) * (if Bt ξ = ζ then 1 else 0) := by
    intro ζ
    rw [hexp, fourier_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [fourier_const_mul, fourier_char]
  unfold l1
  simp only [hF]
  calc ∑ ζ, |∑ ξ, QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ a) * (if Bt ξ = ζ then (1:ℝ) else 0)|
      ≤ ∑ ζ, ∑ ξ, |QAlgorithms.boolFourier f ξ| * (if Bt ξ = ζ then (1:ℝ) else 0) := by
        refine Finset.sum_le_sum fun ζ _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun ξ _ => ?_
        rw [abs_mul, abs_mul, abs_sg, mul_one]
        split_ifs <;> simp
    _ = ∑ ξ, |QAlgorithms.boolFourier f ξ| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [← Finset.mul_sum]
        simp

/-- the sign function of `p` -/
def phase (p : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ℝ := fun x => sg (p x)

lemma phase_sq (p : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) : phase p x ^ 2 = 1 := by
  unfold phase; rw [sq, sg_mul_self]

lemma parseval_phase (p : (Fin n → ZMod 2) → ZMod 2) :
    ∑ ξ, QAlgorithms.boolFourier (phase p) ξ ^ 2 = 1 := by
  rw [parseval]; simp [phase_sq, Finset.card_univ, ZMod.card]

lemma one_le_l1_phase (p : (Fin n → ZMod 2) → ZMod 2) : 1 ≤ l1 (phase p) := by
  have h := fourier_inversion (phase p) 0
  have h0 : |phase p 0| = 1 := abs_sg _
  rw [← h0, h]
  unfold l1
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [abs_mul, abs_sg, mul_one]

def sparsity' (f : (Fin n → ZMod 2) → ℝ) : ℕ :=
  (Finset.univ.filter fun a => QAlgorithms.boolFourier f a ≠ 0).card

lemma sum_eq_sum_filter_ne (F g : (Fin n → ZMod 2) → ℝ) (hg : ∀ ξ, F ξ = 0 → g ξ = 0) :
    ∑ ξ, g ξ = ∑ ξ ∈ Finset.univ.filter (fun a => F a ≠ 0), g ξ := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  split_ifs with h
  · rfl
  · exact hg ξ (not_not.mp h)

lemma l1_sq_le_sparsity (p : (Fin n → ZMod 2) → ZMod 2) :
    l1 (phase p) ^ 2 ≤ sparsity' (phase p) := by
  classical
  have h1 : l1 (phase p) = ∑ ξ ∈ Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0),
      |QAlgorithms.boolFourier (phase p) ξ| * 1 := by
    unfold l1
    rw [sum_eq_sum_filter_ne (QAlgorithms.boolFourier (phase p)) _ (fun ξ h => by simp [h])]
    simp
  rw [h1]
  calc (∑ ξ ∈ Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0),
        |QAlgorithms.boolFourier (phase p) ξ| * 1) ^ 2
      ≤ (∑ ξ ∈ Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0),
          |QAlgorithms.boolFourier (phase p) ξ| ^ 2) *
        (∑ ξ ∈ Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0), (1:ℝ) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ 1 * (Finset.univ.filter (fun a => QAlgorithms.boolFourier (phase p) a ≠ 0)).card := by
        apply mul_le_mul _ (by simp) (by positivity) (by norm_num)
        rw [← parseval_phase p]
        rw [sum_eq_sum_filter_ne (QAlgorithms.boolFourier (phase p))
          (fun ξ => QAlgorithms.boolFourier (phase p) ξ ^ 2) (fun ξ h => by simp [h])]
        exact le_of_eq (Finset.sum_congr rfl fun ξ _ => by rw [sq_abs])
    _ = sparsity' (phase p) := by simp [sparsity']

/-- a phase with at most one nonzero Fourier coefficient is affine -/
lemma affine_of_sparsity_le_one (p : (Fin n → ZMod 2) → ZMod 2) (h : sparsity' (phase p) ≤ 1) :
    ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0 := by
  classical
  have hsupp : ∃ ξ0, ∀ ξ, ξ ≠ ξ0 → QAlgorithms.boolFourier (phase p) ξ = 0 := by
    by_cases he : (Finset.univ.filter fun a => QAlgorithms.boolFourier (phase p) a ≠ 0) = ∅
    · refine ⟨0, fun ξ _ => ?_⟩
      by_contra hne
      have : ξ ∈ Finset.univ.filter fun a => QAlgorithms.boolFourier (phase p) a ≠ 0 := by simp [hne]
      rw [he] at this; simp at this
    · obtain ⟨ξ0, hξ0⟩ := Finset.nonempty_iff_ne_empty.mpr he
      refine ⟨ξ0, fun ξ hξ => ?_⟩
      by_contra hne
      have h2 : ({ξ, ξ0} : Finset _) ⊆
          Finset.univ.filter fun a => QAlgorithms.boolFourier (phase p) a ≠ 0 := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simp [hne]
        · rw [Finset.mem_singleton] at hy; subst hy; exact hξ0
      have := Finset.card_le_card h2
      rw [Finset.card_pair hξ] at this
      unfold sparsity' at h
      omega
  obtain ⟨ξ0, hξ0⟩ := hsupp
  have hval : ∀ x, phase p x = QAlgorithms.boolFourier (phase p) ξ0 * sg (ξ0 ⬝ᵥ x) := by
    intro x
    rw [fourier_inversion (phase p) x, Finset.sum_eq_single ξ0]
    · intro ξ _ hξ; rw [hξ0 ξ hξ, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hp : ∀ x, p x = p 0 + ξ0 ⬝ᵥ x := by
    intro x
    have h1 := hval x
    have h2 := hval 0
    simp only [dotProduct_zero, sg_zero, mul_one] at h2
    rw [← h2] at h1
    unfold phase at h1
    have h3 : sg (p x) = sg (p 0 + ξ0 ⬝ᵥ x) := by rw [sg_add]; exact h1
    have key : ∀ a b : ZMod 2, sg a = sg b → a = b := by
      intro a b hab
      have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;>
        first | rfl | (simp only [sg_zero, sg_one] at hab; norm_num at hab)
    exact key _ _ h3
  intro x u v
  rw [hp (x + u + v), hp (x + u), hp (x + v), hp x]
  simp only [dotProduct_add]
  have h2 : ∀ z : ZMod 2, z + z = 0 := fun z => CharTwo.add_self_eq_zero z
  linear_combination 2 * h2 (p 0) + 2 * h2 (ξ0 ⬝ᵥ x) + h2 (ξ0 ⬝ᵥ u) + h2 (ξ0 ⬝ᵥ v)

end P2MFourier

-- ===== Diffs =====

open scoped BigOperators
noncomputable section

namespace P2MDiff

variable {n : ℕ}

/-- iterated finite differences, as a left fold (first `h 0`, then `h 1`, …) -/
def diffs {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2) :
    (Fin n → ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v x => q (x + v) + q x) p

def dl (u : Fin n → ZMod 2) (q : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 :=
  fun x => q (x + u) + q x

lemma diffs_zero (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin 0 → Fin n → ZMod 2) :
    diffs p h = p := by
  simp [diffs]

lemma diffs_succ {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin (k+1) → Fin n → ZMod 2) :
    diffs p h = diffs (dl (h 0) p) (Fin.tail h) := by
  simp only [diffs, List.ofFn_succ, List.foldl_cons]; rfl

lemma diffs_closed {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (x : Fin n → ZMod 2) :
    diffs p h x = ∑ ε : Fin k → ZMod 2, p (x + ∑ i, ε i • h i) := by
  induction k generalizing p with
  | zero => simp [diffs_zero]
  | succ k ih =>
    rw [diffs_succ, ih]
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => ZMod 2)
      (fun z => p (x + ∑ i, (Fin.cons z.1 z.2 : Fin (k+1) → ZMod 2) i • h i)) _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have h01 : ∀ F : ZMod 2 → ZMod 2, ∑ b : ZMod 2, F b = F 0 + F 1 := by
      intro F
      have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
      rw [this, Finset.sum_pair (by decide)]
    rw [h01, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε' _ => ?_
    simp only [dl, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, zero_smul, one_smul,
      zero_add]
    rw [add_comm (p _)]
    congr 2
    abel

lemma dl_comm (u v : Fin n → ZMod 2) (q : (Fin n → ZMod 2) → ZMod 2) :
    dl u (dl v q) = dl v (dl u q) := by
  funext x; simp only [dl]
  rw [show x + u + v = x + v + u by abel]
  abel

lemma diffs_perm {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (σ : Equiv.Perm (Fin k)) : diffs p (h ∘ σ) = diffs p h := by
  funext x
  rw [diffs_closed, diffs_closed]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl _)) _ _ fun ε => ?_
  congr 2
  have he : (Equiv.arrowCongr σ (Equiv.refl (ZMod 2))) ε = ε ∘ σ.symm := rfl
  rw [he]
  rw [← Equiv.sum_comp σ (fun i => (ε ∘ σ.symm) i • h i)]
  simp

lemma diffs_snoc {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (u : Fin n → ZMod 2) : diffs p (Fin.snoc h u) = dl u (diffs p h) := by
  rw [diffs, List.ofFn_succ', List.concat_eq_append, List.foldl_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.foldl_cons, List.foldl_nil]
  rfl

/-- `p` has degree at most `j`: all `(j+1)`-fold differences vanish -/
def DegLe (j : ℕ) (p : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∀ (h : Fin (j+1) → Fin n → ZMod 2) (x : Fin n → ZMod 2), diffs p h x = 0

lemma diffs_const {j : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe j p)
    (h : Fin j → Fin n → ZMod 2) (x : Fin n → ZMod 2) : diffs p h x = diffs p h 0 := by
  have := hp (Fin.snoc h x) 0
  rw [diffs_snoc] at this
  simp only [dl, zero_add] at this
  have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact h2 _ _ this

lemma top_add_last {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe (k+1) p)
    (h : Fin k → Fin n → ZMod 2) (u v : Fin n → ZMod 2) :
    diffs p (Fin.snoc h (u + v)) 0 = diffs p (Fin.snoc h u) 0 + diffs p (Fin.snoc h v) 0 := by
  rw [diffs_snoc, diffs_snoc, diffs_snoc]
  have h2 := hp (Fin.snoc (Fin.snoc h u) v) 0
  rw [diffs_snoc, diffs_snoc] at h2
  simp only [dl, zero_add] at h2 ⊢
  have e : ∀ a b c d : ZMod 2, a + b + c + d = 0 → a + d = (c + d) + (b + d) := by decide
  apply e
  rw [show u + v = v + u by abel]
  linear_combination h2

end P2MDiff

-- ===== Diffs2 =====

open scoped BigOperators
open ParityDegreeDepth.Core
noncomputable section

namespace P2MDiff

variable {n : ℕ}

lemma diffs_cons {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2)
    (h : Fin k → Fin n → ZMod 2) : diffs p (Fin.cons u h) = diffs (dl u p) h := by
  rw [diffs_succ]; rfl

lemma degLe_dl {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe (k+1) p) (u : Fin n → ZMod 2) :
    DegLe k (dl u p) := by
  intro h x
  rw [← diffs_cons]; exact hp _ x

lemma degLe_succ {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe k p) : DegLe (k+1) p := by
  intro h x
  rw [← Fin.snoc_init_self h, diffs_snoc]
  simp only [dl]
  rw [hp (Fin.init h), hp (Fin.init h), add_zero]

lemma diffs_dl {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2)
    (g : Fin k → Fin n → ZMod 2) : diffs (dl u p) g = dl u (diffs p g) := by
  funext x
  simp only [diffs_closed, dl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [show x + ∑ i, ε i • g i + u = x + u + ∑ i, ε i • g i by abel]

/-- additive maps on `𝔽₂ⁿ` are linear -/
lemma additive_expand (L : (Fin n → ZMod 2) → ZMod 2) (hL : ∀ u v, L (u + v) = L u + L v)
    (w : Fin n → ZMod 2) : L w = ∑ v, w v * L (Pi.single v 1) := by
  have h0 : L 0 = 0 := by
    have := hL 0 0
    simp only [add_zero] at this
    have h2 : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
    exact h2 _ this
  let Lh : (Fin n → ZMod 2) →+ ZMod 2 := ⟨⟨L, h0⟩, hL⟩
  have hw : w = ∑ v, w v • (Pi.single v 1 : Fin n → ZMod 2) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  change Lh _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 (w v) with h | h
  · rw [h, zero_smul, map_zero, zero_mul]
  · rw [h, one_smul, one_mul]; rfl

/-- coefficient tensor of the top form -/
def cT (p : (Fin n → ZMod 2) → ZMod 2) (j : ℕ) : (Fin j → Fin n) → ZMod 2 :=
  fun a => diffs p (fun l => Pi.single (a l) 1) 0

lemma top_eq_tensorEval : ∀ (k : ℕ) (p : (Fin n → ZMod 2) → ZMod 2), DegLe k p →
    ∀ h : Fin k → Fin n → ZMod 2, diffs p h 0 = tensorEval (cT p k) h := by
  intro k
  induction k with
  | zero =>
    intro p _ h
    simp only [tensorEval, cT, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty,
      mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1 <;> funext l <;> exact Fin.elim0 l
  | succ k ih =>
    intro p hp h
    rw [← Fin.snoc_init_self h]
    generalize Fin.init h = g
    generalize h (Fin.last k) = w
    have hlin : ∀ u v, diffs p (Fin.snoc g (u + v)) 0 =
        diffs p (Fin.snoc g u) 0 + diffs p (Fin.snoc g v) 0 := top_add_last hp g
    rw [additive_expand (fun u => diffs p (Fin.snoc g u) 0) hlin w]
    have hstep : ∀ v, diffs p (Fin.snoc g (Pi.single v 1)) 0 =
        ∑ a : Fin k → Fin n, (∏ l, g l (a l)) * cT p (k+1) (Fin.snoc a v) := by
      intro v
      rw [diffs_snoc, ← diffs_dl, ih _ (degLe_dl hp _) g]
      simp only [tensorEval, Algebra.algebraMap_self, RingHom.id_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm]
      congr 1
      simp only [cT]
      rw [diffs_dl, ← diffs_snoc]
      congr 2
      funext l
      refine Fin.lastCases ?_ (fun l' => ?_) l <;> simp
    simp only [hstep]
    simp only [tensorEval, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin n)
      (fun z => cT p (k+1) (Fin.snoc z.2 z.1) * ∏ l, (Fin.snoc g w : Fin (k+1) → Fin n → ZMod 2) l
        ((Fin.snoc z.2 z.1 : Fin (k+1) → Fin n) l)) _ (fun z => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

lemma cT_symm (p : (Fin n → ZMod 2) → ZMod 2) (j : ℕ) (σ : Equiv.Perm (Fin j))
    (a : Fin j → Fin n) : cT p j (a ∘ σ) = cT p j a := by
  unfold cT
  have := diffs_perm p (fun l => (Pi.single (a l) 1 : Fin n → ZMod 2)) σ
  rw [← this]
  rfl

/-- differences commute with affine reparametrisation -/
lemma diffs_comp {m k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (h : Fin k → Fin m → ZMod 2) (y : Fin m → ZMod 2) :
    diffs (fun y => p (a + B y)) h y = diffs p (fun i => B (h i)) (a + B y) := by
  rw [diffs_closed, diffs_closed]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [map_add, map_sum, map_smul, add_assoc]

end P2MDiff

-- ===== Qspec =====

open scoped BigOperators
open Matrix
noncomputable section

namespace P2MQ

open P2MFourier P2MDiff

variable {n : ℕ}

/-- polar form -/
def pol (q : (Fin n → ZMod 2) → ZMod 2) (u v : Fin n → ZMod 2) : ZMod 2 :=
  q (u + v) + q u + q v + q 0

def polM (q : (Fin n → ZMod 2) → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun a b => pol q (Pi.single a 1) (Pi.single b 1)

variable (q : (Fin n → ZMod 2) → ZMod 2)
  (hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
    q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0)

include hq in
lemma pol_add_right (u v w : Fin n → ZMod 2) : pol q u (v + w) = pol q u v + pol q u w := by
  unfold pol
  have h := hq 0 u v w
  simp only [zero_add] at h
  have e : ∀ a b c d e f g h' : ZMod 2,
      a + b + c + d + e + f + g + h' = 0 → a + e + d + h' = (b + e + f + h') + (c + e + g + h') := by
    decide
  rw [show u + (v + w) = u + v + w by abel]
  exact e _ _ _ _ _ _ _ _ h

lemma pol_symm (u v : Fin n → ZMod 2) : pol q u v = pol q v u := by
  unfold pol; rw [add_comm u v]; ring

include hq in
lemma pol_bilin (u v : Fin n → ZMod 2) : pol q u v = u ⬝ᵥ (polM q *ᵥ v) := by
  have h1 : ∀ u, pol q u v = ∑ b, v b * pol q u (Pi.single b 1) := fun u =>
    additive_expand (fun v => pol q u v) (pol_add_right q hq u) v
  have h2 : ∀ b, pol q u (Pi.single b 1) = ∑ a, u a * pol q (Pi.single a 1) (Pi.single b 1) := by
    intro b
    rw [pol_symm]
    rw [additive_expand (fun u => pol q (Pi.single b 1) u) (pol_add_right q hq _) u]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pol_symm]
  rw [h1]
  simp only [h2, dotProduct, mulVec, polM, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- the radical -/
def radF (q : (Fin n → ZMod 2) → ZMod 2) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter fun h => polM q *ᵥ h = 0

include hq in
lemma fourier_sq (ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (phase q) ξ ^ 2 =
      ((2 : ℝ) ^ n)⁻¹ * ∑ h ∈ radF q, sg (ξ ⬝ᵥ h + q h + q 0) := by
  classical
  have h2 : ∀ z : ZMod 2, z + z = 0 := fun z => CharTwo.add_self_eq_zero z
  set c : ℝ := ((2 : ℝ) ^ n)⁻¹
  have hterm : ∀ x h : Fin n → ZMod 2,
      (phase q x * sg (ξ ⬝ᵥ x)) * (phase q (x + h) * sg (ξ ⬝ᵥ (x + h))) =
        sg (ξ ⬝ᵥ h + q h + q 0) * sg ((polM q *ᵥ h) ⬝ᵥ x) := by
    intro x h
    unfold phase
    rw [← sg_add, ← sg_add, ← sg_add, ← sg_add]
    congr 1
    have hpol : (polM q *ᵥ h) ⬝ᵥ x = q (x + h) + q x + q h + q 0 := by
      rw [dotProduct_comm, ← pol_bilin q hq]; rfl
    rw [hpol, dot_add_right]
    linear_combination h2 (ξ ⬝ᵥ x) - h2 (q h) - h2 (q 0)
  calc QAlgorithms.boolFourier (phase q) ξ ^ 2
      = c * c * ∑ x, ∑ y, (phase q x * sg (ξ ⬝ᵥ x)) * (phase q y * sg (ξ ⬝ᵥ y)) := by
        rw [sq, boolFourier_eq, mul_mul_mul_comm, Finset.sum_mul_sum]
    _ = c * c * ∑ x, ∑ h, (phase q x * sg (ξ ⬝ᵥ x)) * (phase q (x + h) * sg (ξ ⬝ᵥ (x + h))) := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        exact (Equiv.sum_comp (Equiv.addLeft x)
          (fun y => (phase q x * sg (ξ ⬝ᵥ x)) * (phase q y * sg (ξ ⬝ᵥ y)))).symm
    _ = c * c * ∑ h, sg (ξ ⬝ᵥ h + q h + q 0) * ∑ x, sg ((polM q *ᵥ h) ⬝ᵥ x) := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => hterm x h
    _ = c * c * ∑ h, (if polM q *ᵥ h = 0 then sg (ξ ⬝ᵥ h + q h + q 0) * (2 : ℝ) ^ n else 0) := by
        congr 1
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [sum_sg_dot]
        split_ifs <;> simp
    _ = c * ∑ h ∈ radF q, sg (ξ ⬝ᵥ h + q h + q 0) := by
        rw [radF, Finset.sum_filter]
        rw [mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun h _ => ?_
        split_ifs
        · simp only [c]; field_simp
        · simp

lemma mem_radF (h : Fin n → ZMod 2) : h ∈ radF q ↔ polM q *ᵥ h = 0 := by
  simp [radF]

lemma radF_add {h h' : Fin n → ZMod 2} (hh : h ∈ radF q) (hh' : h' ∈ radF q) : h + h' ∈ radF q := by
  rw [mem_radF] at *
  rw [mulVec_add, hh, hh', add_zero]

include hq in
lemma char_sum_rad (ξ : Fin n → ZMod 2) :
    (∑ h ∈ radF q, sg (ξ ⬝ᵥ h + q h + q 0) = 0) ∨
      (∑ h ∈ radF q, sg (ξ ⬝ᵥ h + q h + q 0) = (radF q).card) := by
  classical
  have h2 : ∀ z : ZMod 2, z + z = 0 := fun z => CharTwo.add_self_eq_zero z
  set ψ : (Fin n → ZMod 2) → ZMod 2 := fun h => ξ ⬝ᵥ h + q h + q 0
  have hadd : ∀ h ∈ radF q, ∀ h' ∈ radF q, ψ (h + h') = ψ h + ψ h' := by
    intro h hh h' hh'
    have hp : pol q h h' = 0 := by
      rw [pol_bilin q hq, (mem_radF q h').mp hh', dotProduct_zero]
    unfold pol at hp
    simp only [ψ, dot_add_right]
    linear_combination hp - h2 (q h) - h2 (q h') - h2 (q 0)
  by_cases hall : ∀ h ∈ radF q, ψ h = 0
  · right
    rw [Finset.sum_congr rfl (fun h hh => by rw [show ξ ⬝ᵥ h + q h + q 0 = ψ h from rfl, hall h hh])]
    simp [sg_zero]
  · left
    push Not at hall
    obtain ⟨h0, hh0, hψ⟩ := hall
    have hψ1 : ψ h0 = 1 := zmod2_eq_one _ hψ
    set S := ∑ h ∈ radF q, sg (ψ h)
    have hS : S = -S := by
      have : S = ∑ h ∈ radF q, sg (ψ (h + h0)) := by
        refine Finset.sum_nbij' (· + h0) (· + h0) ?_ ?_ ?_ ?_ ?_
        · intro h hh; exact radF_add q hh hh0
        · intro h hh; exact radF_add q hh hh0
        · intro h _; simp [add_assoc, pself]
        · intro h _; simp [add_assoc, pself]
        · intro h _; simp [add_assoc, pself]
      conv_lhs => rw [this]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [hadd h hh h0 hh0, sg_add, hψ1, sg_one]; ring
    have : S = 0 := by linarith
    exact this

lemma card_radF : ((radF q).card : ℝ) * 2 ^ (polM q).rank = 2 ^ n := by
  classical
  have hk : (radF q).card = Fintype.card (LinearMap.ker (polM q).mulVecLin) := by
    rw [radF, ← Fintype.card_subtype]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun h => by simp [LinearMap.mem_ker, Matrix.mulVecLin_apply])
  have hc : Fintype.card (LinearMap.ker (polM q).mulVecLin) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (polM q).mulVecLin) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]; simp [ZMod.card]
  have hr : (polM q).rank + Module.finrank (ZMod 2) (LinearMap.ker (polM q).mulVecLin) = n := by
    rw [Matrix.rank]
    rw [LinearMap.finrank_range_add_finrank_ker]
    simp
  rw [hk, hc]
  push_cast
  rw [← pow_add, add_comm, hr]

include hq in
theorem qspec : l1 (phase q) ^ 2 = 2 ^ (polM q).rank := by
  classical
  set F := QAlgorithms.boolFourier (phase q) with hF
  set C : ℝ := ((radF q).card : ℝ) with hC
  have hCpos : 0 < C := by
    have : (0 : Fin n → ZMod 2) ∈ radF q := by simp [radF]
    have := Finset.card_pos.mpr ⟨_, this⟩
    rw [hC]; exact_mod_cast this
  set c : ℝ := ((2 : ℝ) ^ n)⁻¹ * C with hcdef
  have hcpos : 0 < c := by positivity
  have hsq : ∀ ξ, F ξ ^ 2 = 0 ∨ F ξ ^ 2 = c := by
    intro ξ
    rw [hF, fourier_sq q hq ξ]
    rcases char_sum_rad q hq ξ with h | h
    · left; rw [h, mul_zero]
    · right; rw [h]
  have hpars : ∑ ξ, F ξ ^ 2 = 1 := parseval_phase q
  set N : ℕ := (Finset.univ.filter fun ξ => F ξ ≠ 0).card with hN
  have hsum2 : ∑ ξ, F ξ ^ 2 = N * c := by
    rw [sum_eq_sum_filter_ne F (fun ξ => F ξ ^ 2) (fun ξ h => by simp [h])]
    rw [Finset.sum_congr rfl (fun ξ hξ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
      rcases hsq ξ with h | h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hξ
      · exact h)]
    simp [hN]
  have hsum1 : l1 (phase q) = N * Real.sqrt c := by
    unfold l1
    rw [← hF]
    rw [sum_eq_sum_filter_ne F (fun ξ => |F ξ|) (fun ξ h => by simp [h])]
    rw [Finset.sum_congr rfl (fun ξ hξ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
      rcases hsq ξ with h | h
      · exact absurd ((pow_eq_zero_iff (two_ne_zero)).mp h) hξ
      · rw [← Real.sqrt_sq_eq_abs, h])]
    simp [hN]
  have hNc : (N : ℝ) * c = 1 := by rw [← hsum2, hpars]
  have hcard := card_radF q
  rw [hsum1, mul_pow, Real.sq_sqrt hcpos.le, sq, mul_assoc, hNc, mul_one]
  have hc2 : c * 2 ^ (polM q).rank = 1 := by
    rw [hcdef, mul_assoc, hcard]; field_simp
  calc (N : ℝ) = N * (c * 2 ^ (polM q).rank) := by rw [hc2, mul_one]
    _ = (N * c) * 2 ^ (polM q).rank := by ring
    _ = 2 ^ (polM q).rank := by rw [hNc, one_mul]

end P2MQ

-- ===== adapter =====
open ParityDegreeDepth.Core in
theorem solution {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2)
    (hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0) :
    (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (q x).val) ξ|) ^ 2 =
      2 ^ (Matrix.of fun a b : Fin n =>
        q (Pi.single a 1 + Pi.single b 1) + q (Pi.single a 1) + q (Pi.single b 1) + q 0).rank := by
  exact P2MQ.qspec q hq

