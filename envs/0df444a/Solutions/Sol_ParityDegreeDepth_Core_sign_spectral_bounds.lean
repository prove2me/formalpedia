-- Prove2me | solution 1 for ParityDegreeDepth.Core.sign_spectral_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:59:58.225664+00:00
-- url     : https://prove2.me/submissions/8753447e-4f58-4dd0-bdb6-5f0d3baee666

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier

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

-- ===== adapter =====

theorem solution {n : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) :
    1 ≤ ∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ| ∧
    (∑ ξ, |QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ|) ^ 2 ≤
      ((Finset.univ.filter fun ξ => QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ ≠ 0).card : ℝ) ∧
    ((Finset.univ.filter fun ξ => QAlgorithms.boolFourier (fun x => (-1 : ℝ) ^ (p x).val) ξ ≠ 0).card ≤ 1 →
      ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0) := by
  refine ⟨P2MFourier.one_le_l1_phase p, P2MFourier.l1_sq_le_sparsity p, ?_⟩
  intro h
  exact P2MFourier.affine_of_sparsity_le_one p h

