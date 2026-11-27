-- Prove2me | solution 1 for ParityDegreeDepth.Main.Supplement.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:42:57.6042+00:00
-- url     : https://prove2.me/submissions/30b0d3b5-b729-494a-bdaf-a2ed5a640324

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_ParityDegreeDepth_Core_tensorEval
import Definitions.Def_ParityDegreeDepth_Main_Context
import Definitions.Def_ParityDegreeDepth_Main_Supplement_ThresholdWeight

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

-- ===== ANF =====

open scoped BigOperators
noncomputable section

namespace P2MANF

open P2MDiff

variable {n : ℕ}

/-- the ANF coefficient as in the source statement -/
def coeffZ (p : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

def ind (B : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ B then 1 else 0

lemma natCast_zmod2 (k : ℕ) : (k : ZMod 2) = if Odd k then 1 else 0 := by
  split_ifs with h
  · exact ZMod.natCast_eq_one_iff_odd.mpr h
  · rw [ZMod.natCast_eq_zero_iff_even]; exact Nat.not_odd_iff_even.mp h

lemma coeffZ_eq (p : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) :
    coeffZ p S = ∑ B ∈ S.powerset, p (ind B) := by
  classical
  have h01 : ∀ z : ZMod 2, (if z ≠ 0 then (1 : ZMod 2) else 0) = z := by decide
  rw [← Finset.sum_congr rfl (fun B _ => h01 (p (ind B))), ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one, natCast_zmod2]
  unfold coeffZ ParityCubes.anfCoeff
  have : ∀ B : Finset (Fin n), (fun i => if decide (i ∈ B) = true then (1 : ZMod 2) else 0) = ind B := by
    intro B; funext i; simp [ind]
  simp only [this, decide_eq_true_eq]
  congr

/-- affine phases have no ANF coefficients of size `≥ 2` -/
lemma coeffZ_affine (p : (Fin n → ZMod 2) → ZMod 2)
    (hp : ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) : coeffZ p S = 0 := by
  classical
  rw [coeffZ_eq]
  obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set T := S.erase a
  have hS' : S = insert a T := (Finset.insert_erase ha).symm
  have haT : a ∉ T := Finset.notMem_erase a S
  have hT : T.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
  rw [hS', Finset.sum_powerset_insert haT]
  rw [← Finset.sum_add_distrib]
  have hc : ∀ B ∈ T.powerset, p (ind B) + p (ind (insert a B)) = p (Pi.single a 1) + p 0 := by
    intro B hB
    have haB : a ∉ B := fun h => haT (Finset.mem_powerset.mp hB h)
    have hind : ind (insert a B) = ind B + Pi.single a 1 := by
      funext i; by_cases hi : i = a
      · subst hi; simp [ind, haB]
      · simp [ind, hi, Pi.single_apply]
    rw [hind]
    have := hp 0 (ind B) (Pi.single a 1)
    simp only [zero_add] at this
    have e : ∀ w x y z : ZMod 2, w + x + y + z = 0 → x + w = y + z := by decide
    exact e _ _ _ _ this
  rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  have : ((2 ^ T.card : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_pow (Finset.card_pos.mpr hT).ne']
  rw [this, zero_mul]

end P2MANF

namespace P2MANF

open P2MDiff

variable {n : ℕ}

lemma degLe_iff_succ (k : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) :
    DegLe (k+1) f ↔ ∀ u, DegLe k (dl u f) := by
  constructor
  · intro hf u; exact degLe_dl hf u
  · intro H h x
    rw [diffs_succ]; exact H (h 0) (Fin.tail h) x

lemma degLe_zero_iff (f : (Fin n → ZMod 2) → ZMod 2) :
    DegLe 0 f ↔ ∀ u x, f (x + u) = f x := by
  have e : ∀ h : Fin 1 → Fin n → ZMod 2, diffs f h = dl (h 0) f := by
    intro h; rw [diffs_succ, diffs_zero]
  constructor
  · intro hf u x
    have := hf (fun _ => u) x
    rw [e] at this
    simp only [dl] at this
    have e2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact e2 _ _ this
  · intro H h x
    rw [e]; simp only [dl, H]
    exact CharTwo.add_self_eq_zero _

lemma diffs_add {k : ℕ} (f g : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2) (x : Fin n → ZMod 2) :
    diffs (fun y => f y + g y) h x = diffs f h x + diffs g h x := by
  simp only [diffs_closed, Finset.sum_add_distrib]

lemma degLe_add {k : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) (hg : DegLe k g) :
    DegLe k (fun y => f y + g y) := by
  intro h x; rw [diffs_add, hf, hg, add_zero]

lemma degLe_zerofun (k : ℕ) : DegLe k (fun _ : Fin n → ZMod 2 => (0 : ZMod 2)) := by
  intro h x; simp [diffs_closed]

lemma degLe_smul {k : ℕ} (c : ZMod 2) {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) :
    DegLe k (fun y => c * f y) := by
  intro h x
  simp only [diffs_closed, ← Finset.mul_sum]
  rw [← diffs_closed, hf, mul_zero]

lemma degLe_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ZMod 2)
    (hf : ∀ i ∈ s, DegLe k (f i)) : DegLe k (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degLe_zerofun k
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact degLe_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma degLe_translate {k : ℕ} {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) (u : Fin n → ZMod 2) :
    DegLe k (fun x => f (x + u)) := by
  intro h x
  have := hf h (x + u)
  rw [diffs_closed] at this ⊢
  rw [← this]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1; abel

lemma degLe_mono {k k' : ℕ} (hkk : k ≤ k') {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) :
    DegLe k' f := by
  induction hkk with
  | refl => exact hf
  | step _ ih => exact degLe_succ ih

lemma dl_mul (u : Fin n → ZMod 2) (g h : (Fin n → ZMod 2) → ZMod 2) :
    dl u (fun x => g x * h x) = fun x => dl u g x * h (x + u) + g x * dl u h x := by
  funext x
  simp only [dl]
  have h2 := CharTwo.add_self_eq_zero (g x * h (x + u))
  linear_combination (-1 : ZMod 2) * h2

lemma degLe_mul : ∀ (N a b : ℕ) (g h : (Fin n → ZMod 2) → ZMod 2), a + b = N → DegLe a g →
    DegLe b h → DegLe N (fun x => g x * h x) := by
  intro N
  induction N with
  | zero =>
    intro a b g h hab hg hh
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    rw [degLe_zero_iff] at *
    intro u x
    rw [hg, hh]
  | succ N ih =>
    intro a b g h hab hg hh
    rw [degLe_iff_succ]
    intro u
    rw [dl_mul]
    apply degLe_add
    · cases a with
      | zero =>
        have : ∀ x, dl u g x = 0 := by
          intro x; simp only [dl]; rw [(degLe_zero_iff g).mp hg u x]
          exact CharTwo.add_self_eq_zero _
        simp only [this, zero_mul]
        exact degLe_zerofun N
      | succ a =>
        exact ih a b (dl u g) (fun x => h (x + u)) (by omega) (degLe_dl hg u) (degLe_translate hh u)
    · cases b with
      | zero =>
        have : ∀ x, dl u h x = 0 := by
          intro x; simp only [dl]; rw [(degLe_zero_iff h).mp hh u x]
          exact CharTwo.add_self_eq_zero _
        simp only [this, mul_zero]
        exact degLe_zerofun N
      | succ b =>
        exact ih a b g (dl u h) (by omega) hg (degLe_dl hh u)

def mon (S : Finset (Fin n)) : (Fin n → ZMod 2) → ZMod 2 := fun x => ∏ i ∈ S, x i

lemma degLe_mon (S : Finset (Fin n)) : DegLe S.card (mon S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [mon, Finset.prod_empty, Finset.card_empty]
    rw [degLe_zero_iff]; intro u x; rfl
  | insert a S ha ih =>
    have hcoord : DegLe 1 (fun x : Fin n → ZMod 2 => x a) := by
      rw [degLe_iff_succ]; intro u
      rw [degLe_zero_iff]; intro v x
      simp only [dl, Pi.add_apply]
      linear_combination CharTwo.add_self_eq_zero (v a)
    have := degLe_mul (1 + S.card) 1 S.card _ _ rfl hcoord ih
    rw [Finset.card_insert_of_notMem ha, add_comm]
    convert this using 1
    funext x
    simp [mon, Finset.prod_insert ha]

lemma mobius (T : Finset (Fin n)) : ∀ g : Finset (Fin n) → ZMod 2,
    ∑ S ∈ T.powerset, ∑ B ∈ S.powerset, g B = g T := by
  classical
  induction T using Finset.induction_on with
  | empty => intro g; simp
  | insert a T ha ih =>
    intro g
    rw [Finset.sum_powerset_insert ha]
    have h1 : ∀ S ∈ T.powerset, ∑ B ∈ (insert a S).powerset, g B =
        ∑ B ∈ S.powerset, g B + ∑ B ∈ S.powerset, g (insert a B) := by
      intro S hS
      have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
      rw [Finset.sum_powerset_insert haS]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih (fun B => g (insert a B))]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

lemma inversion (p : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) :
    p x = ∑ S, coeffZ p S * mon S x := by
  classical
  set T := Finset.univ.filter fun i => x i ≠ 0
  have hx : x = ind T := by
    funext i
    simp only [ind, T, Finset.mem_filter, Finset.mem_univ, true_and]
    have h01 : ∀ z : ZMod 2, z = if z ≠ 0 then 1 else 0 := by decide
    exact h01 (x i)
  have hmon : ∀ S, mon S x = if S ⊆ T then 1 else 0 := by
    intro S
    rw [hx]
    simp only [mon, ind]
    split_ifs with h
    · exact Finset.prod_eq_one fun i hi => by simp [h hi]
    · rw [Finset.not_subset] at h
      obtain ⟨i, hiS, hiT⟩ := h
      exact Finset.prod_eq_zero hiS (by simp [hiT])
  simp only [hmon, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun S : Finset (Fin n) => S ⊆ T) = T.powerset := by
    ext S; simp
  rw [this]
  simp only [coeffZ_eq]
  rw [mobius T (fun B => p (ind B)), ← hx]

/-- ANF degree at most `d` implies vanishing `(d+1)`-fold differences -/
theorem degLe_of_coeffZ {d : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (h : ∀ S : Finset (Fin n), d < S.card → coeffZ p S = 0) : DegLe d p := by
  have hp : p = fun x => ∑ S, coeffZ p S * mon S x := funext (inversion p)
  rw [hp]
  apply degLe_sum
  intro S _
  by_cases hS : d < S.card
  · simp only [h S hS, zero_mul]; exact degLe_zerofun d
  · exact degLe_smul _ (degLe_mono (by omega) (degLe_mon S))

end P2MANF

-- ===== T35b =====

open Matrix

namespace T35aux

section rank
variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

theorem exists_li_cols (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ c : Fin k → n, LinearIndependent K (fun j => A.col (c j)) := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have hbfin : b.Finite := (Set.finite_range A.col).subset hb
  have : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = k := by
    have h1 := finrank_span_eq_card (R := K) hli
    rw [Subtype.range_coe, hspan, ← Matrix.rank_eq_finrank_span_cols, hk] at h1
    exact h1.symm
  let e : Fin k ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hchoice : ∀ x : b, ∃ j, A.col j = x := fun x => hb x.2
  choose c hc using hchoice
  refine ⟨fun j => c (e j), ?_⟩
  have : (fun j => A.col (c (e j))) = fun j => ((e j : b) : m → K) := by
    funext j; exact hc (e j)
  rw [this]
  exact hli.comp e e.injective

theorem exists_minor_of_le_rank [Fintype m] (A : Matrix m n K) {k : ℕ} (hk : k ≤ A.rank) :
    ∃ (r : Fin k → m) (c : Fin k → n), (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨c0, hc0⟩ := exists_li_cols A rfl
  let c : Fin k → n := fun j => c0 (Fin.castLE hk j)
  have hc : LinearIndependent K (fun j => A.col (c j)) :=
    hc0.comp _ (Fin.castLE_injective hk)
  set N : Matrix m (Fin k) K := A.submatrix id c with hN
  have hNcol : N.col = fun j => A.col (c j) := by
    funext j; ext i; rfl
  have hNrank : N.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols, hNcol, finrank_span_eq_card hc, Fintype.card_fin]
  have hNt : Nᵀ.rank = k := by rw [Matrix.rank_transpose, hNrank]
  obtain ⟨r, hr⟩ := exists_li_cols Nᵀ hNt
  refine ⟨r, c, ?_⟩
  have hrows : LinearIndependent K (A.submatrix r c).row := by
    have : (A.submatrix r c).row = fun i => Nᵀ.col (r i) := by
      funext i; ext j; rfl
    rw [this]; exact hr
  have hunit : IsUnit (A.submatrix r c) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

theorem le_rank_of_minor [Fintype m] (A : Matrix m n K) {k : ℕ} (r : Fin k → m) (c : Fin k → n)
    (h : (A.submatrix r c).det ≠ 0) : k ≤ A.rank := by
  classical
  have h1 := Matrix.rank_submatrix_le A r c
  have h2 : (A.submatrix r c).rank = k := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))]
    simp
  omega

end rank

theorem det_map_hom {R S : Type*} [CommRing R] [CommRing S] {k : Type*} [Fintype k] [DecidableEq k]
    (f : R →+* S) (M : Matrix k k R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

theorem adj_map_hom {R S : Type*} [CommRing R] [CommRing S] {k : Type*} [Fintype k] [DecidableEq k]
    (f : R →+* S) (M : Matrix k k R) : (M.map f).adjugate = M.adjugate.map f :=
  (RingHom.map_adjugate f M).symm

section domain
variable {S : Type*} [CommRing S] [IsDomain S] {m n : Type*} [Fintype m] [Fintype n]

local notation "Kf" => FractionRing S

theorem rank_le_of_minors (A : Matrix m n S) (k : ℕ)
    (h : ∀ (r : Fin (k+1) → m) (c : Fin (k+1) → n), (A.submatrix r c).det = 0) :
    (A.map (algebraMap S Kf)).rank ≤ k := by
  by_contra hk
  push Not at hk
  obtain ⟨r, c, hrc⟩ := exists_minor_of_le_rank (A.map (algebraMap S Kf)) (k := k+1) hk
  apply hrc
  rw [show (A.map (algebraMap S Kf)).submatrix r c = (A.submatrix r c).map (algebraMap S Kf) from rfl,
    det_map_hom, h r c, map_zero]

theorem le_rank_of_minor' (A : Matrix m n S) {k : ℕ} (r : Fin k → m) (c : Fin k → n)
    (h : (A.submatrix r c).det ≠ 0) : k ≤ (A.map (algebraMap S Kf)).rank := by
  apply le_rank_of_minor _ r c
  rw [show (A.map (algebraMap S Kf)).submatrix r c = (A.submatrix r c).map (algebraMap S Kf) from rfl,
    det_map_hom]
  exact (map_ne_zero_iff _ (IsFractionRing.injective S Kf)).mpr h

theorem minors_zero_of_rank_le (A : Matrix m n S) {k : ℕ} (hk : (A.map (algebraMap S Kf)).rank ≤ k)
    (r : Fin (k+1) → m) (c : Fin (k+1) → n) : (A.submatrix r c).det = 0 := by
  by_contra h
  have := le_rank_of_minor' A r c h
  omega

end domain

section bordered

theorem det_bordered_field {K : Type*} [Field K] {R : ℕ} (P : Matrix (Fin R) (Fin R) K)
    (hP : P.det ≠ 0) (β γ : Fin R → K) (e : K) :
    (Matrix.fromBlocks P (Matrix.of fun i (_ : Unit) => β i) (Matrix.of fun (_ : Unit) j => γ j)
      (Matrix.of fun (_ : Unit) (_ : Unit) => e)).det = P.det * e - γ ⬝ᵥ (P.adjugate *ᵥ β) := by
  have : Invertible P := Matrix.invertibleOfIsUnitDet P (isUnit_iff_ne_zero.mpr hP)
  have hu : ∀ A : Matrix Unit Unit K, A.det = A () () := fun A => Matrix.det_unique A
  rw [Matrix.det_fromBlocks₁₁, hu]
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.invOf_eq_nonsing_inv, Matrix.inv_def,
    Ring.inverse_eq_inv']
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Fintype.univ_unit,
    Finset.sum_singleton, dotProduct, mulVec]
  rw [mul_sub]
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  field_simp

variable {S : Type*} [CommRing S] [IsDomain S] {n : ℕ}

/-- Bordered-minor identity for a matrix of rank `≤ R` over the fraction field. -/
theorem bordered_identity (M : Matrix (Fin n) (Fin n) S) {R : ℕ}
    (hM : (M.map (algebraMap S (FractionRing S))).rank ≤ R) (I I' : Fin R → Fin n)
    (hP : (M.submatrix I I').det ≠ 0) (x y : Fin n → S) :
    (M.submatrix I I').det * (x ⬝ᵥ (M *ᵥ y)) =
      (fun a => (x ᵥ* M) (I' a)) ⬝ᵥ ((M.submatrix I I').adjugate *ᵥ (fun b => (M *ᵥ y) (I b))) := by
  classical
  let φ := algebraMap S (FractionRing S)
  have hinj : Function.Injective φ := IsFractionRing.injective S (FractionRing S)
  -- the bordered matrix over S
  let X : Matrix (Fin R ⊕ Unit) (Fin n) S :=
    Matrix.of fun r j => Sum.elim (fun b => (Pi.single (I b) 1 : Fin n → S) j) (fun _ => x j) r
  let Y : Matrix (Fin n) (Fin R ⊕ Unit) S :=
    Matrix.of fun j c => Sum.elim (fun a => (Pi.single (I' a) 1 : Fin n → S) j) (fun _ => y j) c
  have hXM : ∀ r j, (X * M) r j = Sum.elim (fun b => M (I b) j) (fun _ => (x ᵥ* M) j) r := by
    intro r j
    rcases r with b | u
    · simp only [X, Matrix.mul_apply, Matrix.of_apply, Sum.elim_inl, Pi.single_apply]
      simp
    · simp only [X, Matrix.mul_apply, Matrix.of_apply, Sum.elim_inr, vecMul, dotProduct]
  have hG : X * M * Y = Matrix.fromBlocks (M.submatrix I I')
      (Matrix.of fun i (_ : Unit) => (M *ᵥ y) (I i))
      (Matrix.of fun (_ : Unit) j => (x ᵥ* M) (I' j))
      (Matrix.of fun (_ : Unit) (_ : Unit) => x ⬝ᵥ (M *ᵥ y)) := by
    ext r c
    rw [Matrix.mul_apply]
    simp only [hXM]
    rcases r with b | u <;> rcases c with a | v
    · simp only [Y, Matrix.of_apply, Sum.elim_inl, Pi.single_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.submatrix_apply]
      simp
    · simp only [Y, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂, mulVec,
        dotProduct]
    · simp only [Y, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Pi.single_apply,
        Matrix.fromBlocks_apply₂₁]
      simp
    · simp only [Y, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂]
      rw [Matrix.dotProduct_mulVec]; rfl
  have hdet0 : (X * M * Y).det = 0 := by
    by_contra hne
    have hmap : ((X * M * Y).map φ).det ≠ 0 := by
      rw [det_map_hom]; exact (map_ne_zero_iff _ hinj).mpr hne
    have hrank : ((X * M * Y).map φ).rank = R + 1 := by
      rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hmap))]
      simp
    have hle : ((X * M * Y).map φ).rank ≤ R := by
      rw [Matrix.map_mul, Matrix.map_mul]
      exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hM)
    omega
  rw [hG] at hdet0
  have hPK : ((M.submatrix I I').map φ).det ≠ 0 := by
    rw [det_map_hom]; exact (map_ne_zero_iff _ hinj).mpr hP
  have key := det_bordered_field ((M.submatrix I I').map φ) hPK
    (fun b => φ ((M *ᵥ y) (I b))) (fun a => φ ((x ᵥ* M) (I' a))) (φ (x ⬝ᵥ (M *ᵥ y)))
  have hmapG : (Matrix.fromBlocks ((M.submatrix I I').map φ)
      (Matrix.of fun i (_ : Unit) => φ ((M *ᵥ y) (I i)))
      (Matrix.of fun (_ : Unit) j => φ ((x ᵥ* M) (I' j)))
      (Matrix.of fun (_ : Unit) (_ : Unit) => φ (x ⬝ᵥ (M *ᵥ y)))) =
      (Matrix.fromBlocks (M.submatrix I I')
      (Matrix.of fun i (_ : Unit) => (M *ᵥ y) (I i))
      (Matrix.of fun (_ : Unit) j => (x ᵥ* M) (I' j))
      (Matrix.of fun (_ : Unit) (_ : Unit) => x ⬝ᵥ (M *ᵥ y))).map φ := by
    rw [Matrix.fromBlocks_map]; rfl
  rw [hmapG, det_map_hom, hdet0, map_zero, det_map_hom] at key
  apply hinj
  have : φ ((M.submatrix I I').det * (x ⬝ᵥ (M *ᵥ y))) =
      φ ((fun a => (x ᵥ* M) (I' a)) ⬝ᵥ ((M.submatrix I I').adjugate *ᵥ (fun b => (M *ᵥ y) (I b)))) := by
    rw [map_mul]
    have h2 : φ ((fun a => (x ᵥ* M) (I' a)) ⬝ᵥ ((M.submatrix I I').adjugate *ᵥ
        (fun b => (M *ᵥ y) (I b)))) = (fun a => φ ((x ᵥ* M) (I' a))) ⬝ᵥ
        (((M.submatrix I I').map φ).adjugate *ᵥ (fun b => φ ((M *ᵥ y) (I b)))) := by
      rw [adj_map_hom]
      simp [dotProduct, mulVec, map_sum, map_mul]
    rw [h2]
    linear_combination -key
  exact this

end bordered

end T35aux

-- ===== L32 =====

open scoped BigOperators
open Matrix
noncomputable section

namespace P2MQ

open P2MFourier P2MDiff

variable {n : ℕ}

lemma diffs_append {k l : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (h' : Fin l → Fin n → ZMod 2) : diffs p (Fin.append h h') = diffs (diffs p h) h' := by
  unfold diffs
  rw [List.ofFn_fin_append, List.foldl_append]

lemma diffs_three (q : (Fin n → ZMod 2) → ZMod 2) (u v w x : Fin n → ZMod 2) :
    diffs q ![u, v, w] x = q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x := by
  simp only [diffs, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]
  rw [show x + w + v + u = x + u + v + w by abel, show x + w + v = x + v + w by abel,
    show x + w + u = x + u + w by abel, show x + v + u = x + u + v by abel]
  ring

lemma diffs_two (q : (Fin n → ZMod 2) → ZMod 2) (u v : Fin n → ZMod 2) :
    diffs q ![u, v] 0 = pol q u v := by
  simp only [diffs, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, pol, zero_add]
  rw [show v + u = u + v by abel]
  ring

lemma phase_dl (p : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2) :
    phase (dl u p) = fun x => phase p (x + u) * phase p x := by
  funext x; simp [phase, dl, sg_add]

lemma l1_phase_diffs : ∀ (k : ℕ) (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2),
    l1 (phase (diffs p h)) ≤ l1 (phase p) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => intro p h; rw [diffs_zero]; simp
  | succ k ih =>
    intro p h
    rw [diffs_succ]
    refine (ih _ _).trans ?_
    have h1 : l1 (phase (dl (h 0) p)) ≤ l1 (phase p) ^ 2 := by
      rw [phase_dl]
      refine (l1_mul_le _ _).trans ?_
      rw [l1_translate (phase p) (h 0), sq]
    calc l1 (phase (dl (h 0) p)) ^ 2 ^ k ≤ (l1 (phase p) ^ 2) ^ 2 ^ k :=
          pow_le_pow_left₀ (l1_nonneg _) h1 _
      _ = l1 (phase p) ^ 2 ^ (k + 1) := by rw [← pow_mul, pow_succ, mul_comm]

/-- Lemma 3.2: the binary contraction ranks of the top form are bounded by the spectral norm -/
theorem contraction_rank_bound {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (hp : DegLe (k+2) p)
    (h : Fin k → Fin n → ZMod 2) :
    ((Matrix.of fun a b : Fin n => diffs p (Fin.append h ![Pi.single a 1, Pi.single b 1]) 0).rank : ℝ)
      ≤ 2 ^ (k+1) * Real.logb 2 (l1 (phase p)) := by
  set q := diffs p h with hqdef
  have hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0 := by
    intro x u v w
    rw [← diffs_three, hqdef, ← diffs_append]
    exact hp _ x
  have hM : (Matrix.of fun a b : Fin n => diffs p (Fin.append h ![Pi.single a 1, Pi.single b 1]) 0)
      = polM q := by
    ext a b
    simp only [Matrix.of_apply, polM]
    rw [diffs_append, diffs_two]
  rw [hM]
  have hspec := qspec q hq
  have hl1 := l1_phase_diffs k p h
  have hpos : 0 < l1 (phase q) := lt_of_lt_of_le one_pos (one_le_l1_phase q)
  have hlog : ((polM q).rank : ℝ) = 2 * Real.logb 2 (l1 (phase q)) := by
    have := congrArg (Real.logb 2) hspec
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    push_cast at this
    linarith
  rw [hlog]
  have h2 : Real.logb 2 (l1 (phase q)) ≤ Real.logb 2 (l1 (phase p) ^ 2 ^ k) :=
    Real.logb_le_logb_of_le (by norm_num) hpos hl1
  rw [Real.logb_pow] at h2
  push_cast at h2
  calc 2 * Real.logb 2 (l1 (phase q)) ≤ 2 * (2 ^ k * Real.logb 2 (l1 (phase p))) := by linarith
    _ = 2 ^ (k+1) * Real.logb 2 (l1 (phase p)) := by ring

end P2MQ

-- ===== LC2a =====

open scoped BigOperators
noncomputable section

namespace P2MLC2

open ParityDegreeDepth.Main ParityDegreeDepth.Main.Supplement P2MFourier

variable {n : ℕ}

lemma spectralNorm_eq (f : Vec n (ZMod 2) → ℝ) : spectralNorm f = l1 f := rfl

lemma spectralNorm_nonneg (f : Vec n (ZMod 2) → ℝ) : 0 ≤ spectralNorm f := l1_nonneg f

/-- polarised Parseval -/
lemma plancherel (f g : (Fin n → ZMod 2) → ℝ) :
    ∑ ξ, QAlgorithms.boolFourier f ξ * QAlgorithms.boolFourier g ξ =
      ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * g x := by
  calc ∑ ξ, QAlgorithms.boolFourier f ξ * QAlgorithms.boolFourier g ξ
      = ∑ ξ, QAlgorithms.boolFourier f ξ * (((2 : ℝ) ^ n)⁻¹ * ∑ x, g x * sg (ξ ⬝ᵥ x)) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [boolFourier_eq g ξ]
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, g x * ∑ ξ, QAlgorithms.boolFourier f ξ * sg (ξ ⬝ᵥ x) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ξ _ => ?_
        ring
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * g x := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← fourier_inversion f x, mul_comm]

/-- `‖ĝ‖₁ ≥ 1 / max|f̂|` for a margin-one witness: if all `|f̂| ≤ M` then `1 ≤ M ‖ĝ‖₁` -/
lemma witness_bound (f g : Vec n (ZMod 2) → ℝ) (hfg : IsSignWitness f g) (M : ℝ)
    (hM : ∀ ξ, |QAlgorithms.boolFourier f ξ| ≤ M) : 1 ≤ M * spectralNorm g := by
  have h1 : 1 ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x, f x * g x := by
    have : ∑ _x : Vec n (ZMod 2), (1 : ℝ) ≤ ∑ x, f x * g x := Finset.sum_le_sum fun x _ => hfg x
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      nsmul_eq_mul, mul_one] at this
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [le_inv_mul_iff₀ h2]
    push_cast at this
    linarith
  rw [← plancherel] at h1
  refine h1.trans ?_
  rw [spectralNorm_eq]
  unfold l1
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun ξ _ => le_abs_self _).trans ?_
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hM ξ) (abs_nonneg _)

lemma witness_set_nonempty (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) :
    {w : ℝ | ∃ g : Vec n (ZMod 2) → ℝ, IsSignWitness f g ∧ spectralNorm g = w}.Nonempty := by
  refine ⟨_, f, fun x => ?_, rfl⟩
  rcases hf x with h | h <;> rw [h] <;> norm_num

lemma witness_set_bdd (f : Vec n (ZMod 2) → ℝ) :
    BddBelow {w : ℝ | ∃ g : Vec n (ZMod 2) → ℝ, IsSignWitness f g ∧ spectralNorm g = w} := by
  refine ⟨0, ?_⟩
  rintro w ⟨g, -, rfl⟩
  exact spectralNorm_nonneg g

lemma W_le (f g : Vec n (ZMod 2) → ℝ) (hfg : IsSignWitness f g) :
    thresholdWeight f ≤ spectralNorm g :=
  csInf_le (witness_set_bdd f) ⟨g, hfg, rfl⟩

lemma le_W (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (c : ℝ)
    (h : ∀ g, IsSignWitness f g → c ≤ spectralNorm g) : c ≤ thresholdWeight f := by
  apply le_csInf (witness_set_nonempty f hf)
  rintro w ⟨g, hg, rfl⟩
  exact h g hg

lemma W_nonneg (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) : 0 ≤ thresholdWeight f :=
  le_W f hf 0 fun g _ => spectralNorm_nonneg g

lemma self_witness (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) : IsSignWitness f f := by
  intro x; rcases hf x with h | h <;> rw [h] <;> norm_num

end P2MLC2

-- ===== LC2b =====

open scoped BigOperators
noncomputable section

namespace P2MLC2

open ParityDegreeDepth.Main ParityDegreeDepth.Main.Supplement P2MFourier

variable {n : ℕ}

lemma sd_succ {k : ℕ} (f : Vec n (ZMod 2) → ℝ) (h : Fin (k+1) → Vec n (ZMod 2)) :
    signDerivatives f h = signDerivatives (fun x => f x * f (x + h 0)) (Fin.tail h) := by
  simp only [signDerivatives, List.ofFn_succ, List.foldl_cons]; rfl

lemma sd_witness : ∀ (k : ℕ) (f g : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
    IsSignWitness f g → IsSignWitness (signDerivatives f h) (signDerivatives g h) := by
  intro k
  induction k with
  | zero => intro f g h hfg; simpa [signDerivatives] using hfg
  | succ k ih =>
    intro f g h hfg
    rw [sd_succ, sd_succ]
    apply ih
    intro x
    have h1 := hfg x
    have h2 := hfg (x + h 0)
    calc (1 : ℝ) ≤ (f x * g x) * (f (x + h 0) * g (x + h 0)) := by nlinarith
      _ = _ := by ring

lemma sd_norm : ∀ (k : ℕ) (g : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
    spectralNorm (signDerivatives g h) ≤ spectralNorm g ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => intro g h; simp [signDerivatives]
  | succ k ih =>
    intro g h
    rw [sd_succ]
    refine (ih _ _).trans ?_
    have h1 : spectralNorm (fun x => g x * g (x + h 0)) ≤ spectralNorm g ^ 2 := by
      refine (l1_mul_le _ _).trans ?_
      rw [show l1 (fun x => g (x + h 0)) = l1 g from l1_translate g (h 0), sq]; rfl
    calc spectralNorm (fun x => g x * g (x + h 0)) ^ 2 ^ k ≤ (spectralNorm g ^ 2) ^ 2 ^ k :=
          pow_le_pow_left₀ (l1_nonneg _) h1 _
      _ = spectralNorm g ^ 2 ^ (k + 1) := by rw [← pow_mul, pow_succ, mul_comm]

lemma W_nonneg' (f : Vec n (ZMod 2) → ℝ) : 0 ≤ thresholdWeight f := by
  apply Real.sInf_nonneg
  rintro w ⟨g, -, rfl⟩
  exact spectralNorm_nonneg g

lemma W_sd {k : ℕ} (f : Vec n (ZMod 2) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (h : Fin k → Vec n (ZMod 2)) :
    thresholdWeight (signDerivatives f h) ≤ thresholdWeight f ^ (2 ^ k) := by
  set a := thresholdWeight (signDerivatives f h)
  set N := 2 ^ k with hN
  have hN0 : N ≠ 0 := by positivity
  have ha0 : 0 ≤ a := W_nonneg' _
  have hroot : a ^ ((N : ℝ)⁻¹) ≤ thresholdWeight f := by
    apply le_W f hf
    intro g hg
    have h1 : a ≤ spectralNorm g ^ N :=
      (W_le _ _ (sd_witness k f g h hg)).trans (sd_norm k g h)
    calc a ^ ((N : ℝ)⁻¹) ≤ (spectralNorm g ^ N) ^ ((N : ℝ)⁻¹) :=
          Real.rpow_le_rpow ha0 h1 (by positivity)
      _ = spectralNorm g := Real.pow_rpow_inv_natCast (spectralNorm_nonneg g) hN0
  calc a = (a ^ ((N : ℝ)⁻¹)) ^ N := (Real.rpow_inv_natCast_pow ha0 hN0).symm
    _ ≤ thresholdWeight f ^ N := pow_le_pow_left₀ (by positivity) hroot _

/-- quadratic phases: all coefficients are at most `2^{-rank/2}` -/
lemma quad_coeff_bound (q : (Fin n → ZMod 2) → ZMod 2)
    (hq : ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0) (ξ : Fin n → ZMod 2) :
    QAlgorithms.boolFourier (P2MFourier.phase q) ξ ^ 2 * 2 ^ (P2MQ.polM q).rank ≤ 1 := by
  rw [P2MQ.fourier_sq q hq ξ]
  have hcard := P2MQ.card_radF q
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rcases P2MQ.char_sum_rad q hq ξ with h | h
  · rw [h]; simp
  · rw [h]
    apply le_of_eq
    calc ((2 : ℝ) ^ n)⁻¹ * ((P2MQ.radF q).card : ℝ) * 2 ^ (P2MQ.polM q).rank
        = ((2 : ℝ) ^ n)⁻¹ * (((P2MQ.radF q).card : ℝ) * 2 ^ (P2MQ.polM q).rank) := by ring
      _ = 1 := by rw [hcard]; field_simp

end P2MLC2

-- ===== LC2c =====

open scoped BigOperators
noncomputable section

namespace P2MLC2

open ParityDegreeDepth.Main ParityDegreeDepth.Main.Supplement

variable {n : ℕ}

lemma phase_pm (p : Vec n (ZMod 2) → ZMod 2) :
    ∀ x, ParityDegreeDepth.Main.phase p x = -1 ∨ ParityDegreeDepth.Main.phase p x = 1 := by
  intro x
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  unfold ParityDegreeDepth.Main.phase
  rcases h01 (p x) with h | h <;> rw [h] <;> simp [ZMod.val_one]

lemma sd_phase : ∀ (k : ℕ) (p : Vec n (ZMod 2) → ZMod 2) (h : Fin k → Vec n (ZMod 2)),
    signDerivatives (ParityDegreeDepth.Main.phase p) h = ParityDegreeDepth.Main.phase (P2MDiff.diffs p h) := by
  intro k
  induction k with
  | zero => intro p h; simp [signDerivatives, P2MDiff.diffs]
  | succ k ih =>
    intro p h
    rw [sd_succ, P2MDiff.diffs_succ, ← ih]
    congr 1
    funext x
    show P2MFourier.sg (p x) * P2MFourier.sg (p (x + h 0)) = P2MFourier.sg (p (x + h 0) + p x)
    rw [P2MFourier.sg_add, mul_comm]

lemma degLe_of_anf_le {k : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (hp : anfDegree p ≤ (k : WithBot ℕ)) :
    P2MDiff.DegLe k p := by
  classical
  apply P2MANF.degLe_of_coeffZ p
  intro S hS
  by_contra hne
  have : ((S.card : ℕ) : WithBot ℕ) ≤ anfDegree p := by
    unfold anfDegree
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun S : Finset (Fin n) =>
      if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ)) (Finset.mem_univ S))
    simp only [show coefficient p S = P2MANF.coeffZ p S from rfl, if_neg hne]
  have := this.trans hp
  have : S.card ≤ k := by exact_mod_cast this
  omega

lemma hq_of_degLe2 (q : Vec n (ZMod 2) → ZMod 2) (hq : P2MDiff.DegLe 2 q) :
    ∀ x u v w : Fin n → ZMod 2, q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x = 0 := by
  intro x u v w; rw [← P2MQ.diffs_three]; exact hq _ x

/-- for a quadratic phase with polar rank `ρ`, every witness has norm at least `√(2^ρ)` -/
lemma quad_witness (q : Vec n (ZMod 2) → ZMod 2) (hq : P2MDiff.DegLe 2 q) (g : Vec n (ZMod 2) → ℝ)
    (hg : IsSignWitness (ParityDegreeDepth.Main.phase q) g) :
    Real.sqrt (2 ^ (P2MQ.polM q).rank) ≤ spectralNorm g := by
  have hq' := hq_of_degLe2 q hq
  have hpos : (0 : ℝ) < Real.sqrt (2 ^ (P2MQ.polM q).rank) := Real.sqrt_pos.mpr (by positivity)
  have hb := witness_bound _ g hg (Real.sqrt (2 ^ (P2MQ.polM q).rank))⁻¹ (by
    intro ξ
    have h1 := quad_coeff_bound q hq' ξ
    have hc : (0 : ℝ) < 2 ^ (P2MQ.polM q).rank := by positivity
    have h2 : QAlgorithms.boolFourier (ParityDegreeDepth.Main.phase q) ξ ^ 2 ≤
        ((Real.sqrt (2 ^ (P2MQ.polM q).rank))⁻¹) ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (by positivity), show ((2 : ℝ) ^ (P2MQ.polM q).rank)⁻¹ =
        1 / 2 ^ (P2MQ.polM q).rank by ring, le_div_iff₀ hc]
      exact h1
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_pos (inv_pos.mpr hpos)] at h3)
  rw [le_inv_mul_iff₀ hpos, mul_one] at hb
  exact hb

lemma polM_eq_contraction (p : Vec n (ZMod 2) → ZMod 2) :
    P2MQ.polM p = contraction (topForm p 2) (fun i => Fin.elim0 i) := by
  ext a b
  simp only [P2MQ.polM, contraction, topForm, Matrix.of_apply]
  rw [← P2MQ.diffs_two]
  show _ = P2MDiff.diffs p _ 0
  congr 1
  funext s
  fin_cases s <;> simp

lemma coeff_eq_top {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (ind : Fin d → Fin n)
    (hind : Function.Injective ind) :
    P2MDiff.diffs p (fun i => Pi.single (ind i) 1) 0 = ParityDegreeDepth.Main.coefficient p (Finset.univ.image ind) := by
  classical
  rw [show ParityDegreeDepth.Main.coefficient p (Finset.univ.image ind) = P2MANF.coeffZ p (Finset.univ.image ind) from rfl,
    P2MANF.coeffZ_eq, P2MDiff.diffs_closed]
  simp only [zero_add]
  refine Finset.sum_nbij' (fun ε => (Finset.univ.filter fun l => ε l = 1).image ind)
    (fun B l => if ind l ∈ B then 1 else 0) ?_ ?_ ?_ ?_ ?_
  · intro ε _
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  · intro B _; simp
  · intro ε _
    funext l
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    by_cases hl : ε l = 1
    · rw [if_pos ⟨l, hl, rfl⟩, hl]
    · rw [if_neg]
      · rcases h01 (ε l) with h | h
        · exact h.symm
        · exact absurd h hl
      · rintro ⟨l', hl', he⟩
        exact hl (hind he ▸ hl')
  · intro B hB
    simp only [Finset.mem_coe, Finset.mem_powerset] at hB
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left_iff,
      zero_ne_one, imp_false, not_not]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact hl
    · intro hv
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp (hB hv)
      exact ⟨l, hv, rfl⟩
  · intro ε _
    congr 1
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, P2MANF.ind, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : ∃ l, ε l = 1 ∧ ind l = v
    · obtain ⟨l, hl, rfl⟩ := hv
      rw [if_pos ⟨l, hl, rfl⟩, Finset.sum_eq_single l]
      · simp [hl]
      · intro b _ hb; rw [if_neg (fun h => hb (hind h.symm))]
      · simp
    · rw [if_neg hv]
      refine Finset.sum_eq_zero fun l _ => ?_
      split_ifs with h
      · have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        rcases h01 (ε l) with h' | h'
        · exact h'
        · exact absurd ⟨l, h', h.symm⟩ hv
      · rfl


theorem lc2 :
    -- (a)
    (∀ (n m : ℕ) (f g : Vec n (ZMod 2) → ℝ)
        (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2)) (a : Vec n (ZMod 2)),
        (∀ x, f x = -1 ∨ f x = 1) → Function.Injective B →
        (IsSignWitness f g →
          IsSignWitness (f ∘ affineMap B a) (g ∘ affineMap B a) ∧
          spectralNorm (g ∘ affineMap B a) ≤ spectralNorm g) ∧
        thresholdWeight (f ∘ affineMap B a) ≤ thresholdWeight f) ∧
    -- (b)
    (∀ (n : ℕ) (f₁ f₂ g₁ g₂ : Vec n (ZMod 2) → ℝ),
        (∀ x, f₁ x = -1 ∨ f₁ x = 1) → (∀ x, f₂ x = -1 ∨ f₂ x = 1) →
        IsSignWitness f₁ g₁ → IsSignWitness f₂ g₂ →
        IsSignWitness (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) ∧
        spectralNorm (fun x => g₁ x * g₂ x) ≤ spectralNorm g₁ * spectralNorm g₂) ∧
    (∀ (n k : ℕ) (f : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
        (∀ x, f x = -1 ∨ f x = 1) →
        thresholdWeight (signDerivatives f h) ≤ thresholdWeight f ^ (2 ^ k)) ∧
    -- (c)
    (∀ (n r : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
        anfDegree p ≤ (2 : WithBot ℕ) →
        (contraction (topForm p 2) (fun i => Fin.elim0 i)).rank = 2 * r →
        (∀ g, IsSignWitness (phase p) g → (2 : ℝ) ^ r ≤ spectralNorm g) ∧
        thresholdWeight (phase p) = (2 : ℝ) ^ r) ∧
    -- (d)
    (∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
        2 ≤ d → anfDegree p = (d : WithBot ℕ) →
        1 < thresholdWeight (phase p)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n m f g B a hf hB
    refine ⟨fun hfg => ⟨fun x => hfg _, P2MFourier.l1_affine g B a⟩, ?_⟩
    apply le_W f hf
    intro g hg
    exact (W_le _ (g ∘ affineMap B a) (fun x => hg _)).trans (P2MFourier.l1_affine g B a)
  · intro n f₁ f₂ g₁ g₂ _ _ h₁ h₂
    refine ⟨fun x => ?_, P2MFourier.l1_mul_le g₁ g₂⟩
    have a1 := h₁ x
    have a2 := h₂ x
    calc (1 : ℝ) ≤ (f₁ x * g₁ x) * (f₂ x * g₂ x) := by nlinarith
      _ = _ := by ring
  · intro n k f h hf
    exact W_sd f hf h
  · intro n r p hp hr
    have hdeg := degLe_of_anf_le (k := 2) p hp
    have hrank : (P2MQ.polM p).rank = 2 * r := by rw [polM_eq_contraction]; exact hr
    have hspec := P2MQ.qspec p (hq_of_degLe2 p hdeg)
    rw [hrank] at hspec
    have hl1 : spectralNorm (ParityDegreeDepth.Main.phase p) = 2 ^ r := by
      have h0 : 0 ≤ spectralNorm (ParityDegreeDepth.Main.phase p) := spectralNorm_nonneg _
      have : spectralNorm (ParityDegreeDepth.Main.phase p) ^ 2 = ((2 : ℝ) ^ r) ^ 2 := by
        rw [← pow_mul, mul_comm]; exact hspec
      exact (pow_left_inj₀ h0 (by positivity) two_ne_zero).mp this
    have hsqrt : Real.sqrt (2 ^ (P2MQ.polM p).rank) = (2 : ℝ) ^ r := by
      rw [hrank, pow_mul', Real.sqrt_sq (by positivity)]
    have hwit : ∀ g, IsSignWitness (ParityDegreeDepth.Main.phase p) g → (2 : ℝ) ^ r ≤ spectralNorm g := by
      intro g hg; rw [← hsqrt]; exact quad_witness p hdeg g hg
    refine ⟨hwit, le_antisymm ?_ (le_W _ (phase_pm p) _ hwit)⟩
    rw [← hl1]
    exact W_le _ _ (self_witness _ (phase_pm p))
  · intro n d p hd hp
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    have hdeg : P2MDiff.DegLe (k + 2) p := degLe_of_anf_le p (le_of_eq hp)
    obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset (Fin n)))
      Finset.univ_nonempty (fun S : Finset (Fin n) =>
        if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ))
    have h1 : anfDegree p = if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ) := hS
    rw [hp] at h1
    split_ifs at h1 with hc
    · exact absurd h1 (WithBot.natCast_ne_bot _)
    have hcard : S.card = k + 2 := by exact_mod_cast h1.symm
    let e := S.equivFin
    let ind : Fin (k + 2) → Fin n := fun i => (e.symm (Fin.cast hcard.symm i) : Fin n)
    have hind : Function.Injective ind := by
      intro a b hab
      have := Subtype.ext hab
      have := e.symm.injective this
      exact Fin.cast_injective _ this
    have himg : Finset.univ.image ind = S := by
      ext v; constructor
      · intro hv; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv; exact (e.symm _).2
      · intro hv
        refine Finset.mem_image.mpr ⟨Fin.cast hcard (e ⟨v, hv⟩), Finset.mem_univ _, ?_⟩
        simp [ind]
    set h : Fin (k + 2) → Vec n (ZMod 2) := fun i => Pi.single (ind i) 1 with hh
    have hT : P2MDiff.diffs p h 0 ≠ 0 := by
      rw [coeff_eq_top p ind hind, himg]; exact hc
    let hk : Fin k → Vec n (ZMod 2) := fun l => h (Fin.castAdd 2 l)
    set q := P2MDiff.diffs p hk with hqdef
    have hsplit : h = Fin.append hk ![h (Fin.natAdd k 0), h (Fin.natAdd k 1)] := by
      funext i
      refine Fin.addCases (fun l => ?_) (fun t => ?_) i
      · simp [hk, Fin.append_left]
      · fin_cases t <;> simp [Fin.append_right]
    have hpol : P2MQ.pol q (h (Fin.natAdd k 0)) (h (Fin.natAdd k 1)) ≠ 0 := by
      rw [← P2MQ.diffs_two, hqdef, ← P2MQ.diffs_append, ← hsplit]; exact hT
    have hrank : 1 ≤ (P2MQ.polM q).rank := by
      apply T35aux.le_rank_of_minor (P2MQ.polM q) (fun _ => ind (Fin.natAdd k 0))
        (fun _ => ind (Fin.natAdd k 1))
      rw [Matrix.det_unique]
      exact hpol
    have hq2 : P2MDiff.DegLe 2 q := by
      intro h' x
      rw [hqdef, ← P2MQ.diffs_append]
      exact hdeg _ x
    have hWq : Real.sqrt 2 ≤ thresholdWeight (ParityDegreeDepth.Main.phase q) := by
      apply le_W _ (phase_pm q)
      intro g hg
      refine le_trans ?_ (quad_witness q hq2 g hg)
      apply Real.sqrt_le_sqrt
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (P2MQ.polM q).rank := pow_le_pow_right₀ (by norm_num) hrank
    have hsd := W_sd (ParityDegreeDepth.Main.phase p) (phase_pm p) hk
    rw [sd_phase] at hsd
    have hsqrt : 1 < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    by_contra hle
    push Not at hle
    have hW0 := W_nonneg' (ParityDegreeDepth.Main.phase p)
    have := pow_le_one₀ hW0 hle (n := 2 ^ k)
    linarith

end P2MLC2

-- ===== adapter =====
open ParityDegreeDepth.Main ParityDegreeDepth.Main.Supplement in
theorem solution :
    -- (a)
    (∀ (n m : ℕ) (f g : Vec n (ZMod 2) → ℝ)
        (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2)) (a : Vec n (ZMod 2)),
        (∀ x, f x = -1 ∨ f x = 1) → Function.Injective B →
        (IsSignWitness f g →
          IsSignWitness (f ∘ affineMap B a) (g ∘ affineMap B a) ∧
          spectralNorm (g ∘ affineMap B a) ≤ spectralNorm g) ∧
        thresholdWeight (f ∘ affineMap B a) ≤ thresholdWeight f) ∧
    -- (b)
    (∀ (n : ℕ) (f₁ f₂ g₁ g₂ : Vec n (ZMod 2) → ℝ),
        (∀ x, f₁ x = -1 ∨ f₁ x = 1) → (∀ x, f₂ x = -1 ∨ f₂ x = 1) →
        IsSignWitness f₁ g₁ → IsSignWitness f₂ g₂ →
        IsSignWitness (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) ∧
        spectralNorm (fun x => g₁ x * g₂ x) ≤ spectralNorm g₁ * spectralNorm g₂) ∧
    (∀ (n k : ℕ) (f : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
        (∀ x, f x = -1 ∨ f x = 1) →
        thresholdWeight (signDerivatives f h) ≤ thresholdWeight f ^ (2 ^ k)) ∧
    -- (c)
    (∀ (n r : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
        anfDegree p ≤ (2 : WithBot ℕ) →
        (contraction (topForm p 2) (fun i => Fin.elim0 i)).rank = 2 * r →
        (∀ g, IsSignWitness (phase p) g → (2 : ℝ) ^ r ≤ spectralNorm g) ∧
        thresholdWeight (phase p) = (2 : ℝ) ^ r) ∧
    -- (d)
    (∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
        2 ≤ d → anfDegree p = (d : WithBot ℕ) →
        1 < thresholdWeight (phase p)) := P2MLC2.lc2

