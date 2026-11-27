-- Prove2me | solution 1 for ParityDegreeDepth.Core.theorem_1_3_public
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:19:10.553138+00:00
-- url     : https://prove2.me/submissions/7f2afcf8-7859-4c71-b50c-270c33569f7e

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_ParityDegreeDepth_Core_Setting
import Definitions.Def_ParityDegreeDepth_Core_tensorEval
import Theorems.Thm_ParityDegreeDepth_Core_quadratic_vanishing_codim
import Theorems.Thm_ParityDegreeDepth_Core_top_form_vanishing_codim
import Theorems.Thm_ParityDegreeDepth_Core_spectral_norm_affine_restriction
import Theorems.Thm_ParityDegreeDepth_Core_sign_spectral_bounds
import Theorems.Thm_ParityDegreeDepth_Core_anf_degree_differences

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

-- ===== MainX =====
noncomputable section
namespace P2MFourier
def phase {n : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ℝ := fun x => sg (p x)
end P2MFourier

namespace P2MX
open P2MDiff
variable {n : ℕ}

lemma diffs_three (q : (Fin n → ZMod 2) → ZMod 2) (u v w x : Fin n → ZMod 2) :
    diffs q ![u, v, w] x = q (x + u + v + w) + q (x + u + v) + q (x + u + w) +
      q (x + v + w) + q (x + u) + q (x + v) + q (x + w) + q x := by
  simp only [diffs, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]
  rw [show x + w + v + u = x + u + v + w by abel, show x + w + v = x + v + w by abel,
    show x + w + u = x + u + w by abel, show x + v + u = x + u + v by abel]
  ring

lemma diffs_two (q : (Fin n → ZMod 2) → ZMod 2) (u v : Fin n → ZMod 2) :
    diffs q ![u, v] 0 = q (u + v) + q u + q v + q 0 := by
  simp only [diffs, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, zero_add]
  rw [show v + u = u + v by abel]
  ring

end P2MX
end

-- ===== adapter =====
open scoped BigOperators
noncomputable section
namespace ParityDegreeDepth.Main

open ParityDegreeDepth.Core.Setting

open Matrix

section trees

variable {n : ℕ}

private lemma treeEval_query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (l r : ParityTree n)
    (x : Vec n (ZMod 2)) :
    treeEval (ParityTree.query a ha l r) x = if a ⬝ᵥ x = 0 then treeEval l x else treeEval r x := rfl

private lemma treeDepth_query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (l r : ParityTree n) :
    treeDepth (ParityTree.query a ha l r) = 1 + max (treeDepth l) (treeDepth r) := rfl

/-- transport of a tree along an injective affine map -/
private lemma transport {m : ℕ} (B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hB : Function.Injective B) (a : Fin n → ZMod 2) :
    ∀ t : ParityTree m, ∃ t' : ParityTree n, treeDepth t' = treeDepth t ∧
      ∀ y, treeEval t' (a + B y) = treeEval t y := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective B (LinearMap.ker_eq_bot.mpr hB)
  intro t
  induction t with
  | leaf b => exact ⟨ParityTree.leaf b, rfl, fun y => rfl⟩
  | query b hb l r ihl ihr =>
    obtain ⟨l', hl'd, hl'⟩ := ihl
    obtain ⟨r', hr'd, hr'⟩ := ihr
    let c : Fin n → ZMod 2 := fun j => b ⬝ᵥ L (Pi.single j 1)
    have hc : ∀ x, c ⬝ᵥ x = b ⬝ᵥ L x := by
      intro x
      have hx : x = ∑ j, x j • (Pi.single j 1 : Fin n → ZMod 2) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hx]
      rw [map_sum, dotProduct_sum]
      simp only [map_smul, c, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hcB : ∀ y, c ⬝ᵥ B y = b ⬝ᵥ y := by
      intro y; rw [hc]
      have := congrArg (fun f => f y) hL
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [this]
    have hc0 : c ≠ 0 := by
      intro h0
      apply hb
      funext i
      have := hcB (Pi.single i 1)
      rw [h0, zero_dotProduct] at this
      simpa [dotProduct_single] using this.symm
    by_cases hca : c ⬝ᵥ a = 0
    · refine ⟨ParityTree.query c hc0 l' r', ?_, ?_⟩
      · rw [treeDepth_query, treeDepth_query, hl'd, hr'd]
      · intro y
        rw [treeEval_query, treeEval_query, dotProduct_add, hca, zero_add, hcB, hl', hr']
    · have hca1 : c ⬝ᵥ a = 1 := P2MFourier.zmod2_eq_one _ hca
      refine ⟨ParityTree.query c hc0 r' l', ?_, ?_⟩
      · rw [treeDepth_query, treeDepth_query, hl'd, hr'd, max_comm]
      · intro y
        rw [treeEval_query, treeEval_query, dotProduct_add, hca1, hcB, hl', hr']
        have h01 : ∀ z : ZMod 2, (1 + z = 0) ↔ ¬ (z = 0) := by decide
        by_cases hz : b ⬝ᵥ y = 0
        · rw [if_neg ((h01 _).not.mpr (not_not.mpr hz)), if_pos hz]
        · rw [if_pos ((h01 _).mpr hz), if_neg hz]

/-- querying a list of parity checks, then using trees on the cells -/
private lemma coset_tree (f : Vec n (ZMod 2) → ℝ) (D : ℕ) (tf : Vec n (ZMod 2) → ParityTree n) :
    ∀ (cs : List (Vec n (ZMod 2))) (S : Set (Vec n (ZMod 2))),
      (∀ a ∈ S, treeDepth (tf a) ≤ D ∧
        ∀ x ∈ S, (∀ c ∈ cs, c ⬝ᵥ x = c ⬝ᵥ a) → treeEval (tf a) x = f x) →
      ∃ t : ParityTree n, treeDepth t ≤ cs.length + D ∧ ∀ x ∈ S, treeEval t x = f x := by
  classical
  intro cs
  induction cs with
  | nil =>
    intro S hS
    by_cases hne : S.Nonempty
    · obtain ⟨a, ha⟩ := hne
      refine ⟨tf a, by simpa using (hS a ha).1, fun x hx => (hS a ha).2 x hx (by simp)⟩
    · refine ⟨ParityTree.leaf true, by simp [treeDepth], fun x hx => absurd ⟨x, hx⟩ hne⟩
  | cons c cs ih =>
    intro S hS
    by_cases hc : c = 0
    · obtain ⟨t, ht, htS⟩ := ih S (fun a ha => ⟨(hS a ha).1, fun x hx hcs =>
        (hS a ha).2 x hx (by
          intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · rw [hc, zero_dotProduct, zero_dotProduct]
          · exact hcs c' hc')⟩)
      exact ⟨t, by simp; omega, htS⟩
    · have hsub : ∀ b : ZMod 2, ∃ t : ParityTree n, treeDepth t ≤ cs.length + D ∧
          ∀ x ∈ {x | x ∈ S ∧ c ⬝ᵥ x = b}, treeEval t x = f x := by
        intro b
        apply ih
        rintro a ⟨haS, hab⟩
        refine ⟨(hS a haS).1, fun x ⟨hxS, hxb⟩ hcs => (hS a haS).2 x hxS ?_⟩
        intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · rw [hxb, hab]
        · exact hcs c' hc'
      obtain ⟨t0, ht0, ht0S⟩ := hsub 0
      obtain ⟨t1, ht1, ht1S⟩ := hsub 1
      refine ⟨ParityTree.query c hc t0 t1, ?_, ?_⟩
      · rw [treeDepth_query]; simp only [List.length_cons]; omega
      · intro x hx
        rw [treeEval_query]
        split_ifs with h
        · exact ht0S x ⟨hx, h⟩
        · exact ht1S x ⟨hx, P2MFourier.zmod2_eq_one _ h⟩

private lemma treeEval_leaf (b : Bool) (x : Vec n (ZMod 2)) :
    treeEval (ParityTree.leaf b : ParityTree n) x = if b then -1 else 1 := rfl

private lemma sg_eq_leaf (v : ZMod 2) : P2MFourier.sg v = if decide (v = 1) then -1 else 1 := by
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 v with rfl | rfl
  · simp [P2MFourier.sg_zero]
  · simp [P2MFourier.sg_one]

/-- affine phases have parity depth at most one -/
private lemma affine_tree (p : Vec n (ZMod 2) → ZMod 2) (hp : P2MDiff.DegLe 1 p) :
    ∃ t : ParityTree n, treeDepth t ≤ 1 ∧ ∀ x, treeEval t x = phase p x := by
  classical
  have hpol : ∀ u v, p (u + v) + p u + p v + p 0 = 0 := by
    intro u v
    have := hp ![u, v] 0
    rw [P2MX.diffs_two] at this
    exact this
  let L : Vec n (ZMod 2) → ZMod 2 := fun x => p x + p 0
  have hL : ∀ u v, L (u + v) = L u + L v := by
    intro u v
    simp only [L]
    have := hpol u v
    linear_combination this - CharTwo.add_self_eq_zero (p u) - CharTwo.add_self_eq_zero (p v) -
      CharTwo.add_self_eq_zero (p 0)
  let ℓ : Vec n (ZMod 2) := fun i => L (Pi.single i 1)
  have hℓ : ∀ x, p x = p 0 + ℓ ⬝ᵥ x := by
    intro x
    have := P2MDiff.additive_expand L hL x
    have hdot : ℓ ⬝ᵥ x = p x + p 0 := by
      rw [dotProduct]
      simp only [L] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 := CharTwo.add_self_eq_zero (p 0)
    linear_combination -hdot - h2
  have hph : ∀ x, phase p x = P2MFourier.sg (p 0 + ℓ ⬝ᵥ x) := by
    intro x; rw [← hℓ]; rfl
  by_cases hℓ0 : ℓ = 0
  · refine ⟨ParityTree.leaf (decide (p 0 = 1)), by simp [treeDepth], fun x => ?_⟩
    rw [hph, hℓ0, zero_dotProduct, add_zero, treeEval_leaf, sg_eq_leaf]
  · refine ⟨ParityTree.query ℓ hℓ0 (ParityTree.leaf (decide (p 0 = 1)))
      (ParityTree.leaf (decide (p 0 + 1 = 1))), by simp [treeDepth], fun x => ?_⟩
    rw [treeEval_query, hph]
    split_ifs with h
    · rw [h, add_zero, treeEval_leaf, sg_eq_leaf]
    · rw [P2MFourier.zmod2_eq_one _ h, treeEval_leaf, sg_eq_leaf]

end trees

section rec

private def Gam (j : ℕ) : ℝ := if j = 2 then 1 else 2 ^ (2 * j - 3)
private def Gs (d : ℕ) : ℝ := ∑ j ∈ Finset.Icc 2 d, Gam j

private lemma Gam_nonneg (j : ℕ) : 0 ≤ Gam j := by unfold Gam; split_ifs <;> positivity

private lemma Gs_nonneg (d : ℕ) : 0 ≤ Gs d := Finset.sum_nonneg fun j _ => Gam_nonneg j

private lemma Gs_succ {d : ℕ} (hd : 1 ≤ d) : Gs (d+1) = Gs d + Gam (d+1) := by
  unfold Gs
  rw [Finset.sum_Icc_succ_top (by omega)]

private lemma Gs_one : Gs 1 = 0 := by simp [Gs]

private lemma Gs_closed : ∀ d, 2 ≤ d → Gs d = ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => simp [Gs, Gam]; norm_num
  | succ d hd ih =>
    rw [Gs_succ (by omega), ih]
    unfold Gam
    rw [if_neg (by omega)]
    rw [show 2 * (d+1) - 1 = (2 * d - 1) + 2 by omega, show 2 * (d+1) - 3 = 2 * d - 1 by omega,
      pow_add]
    ring

variable {n : ℕ}

private lemma l1_pos (p : Vec n (ZMod 2) → ZMod 2) : 0 < P2MFourier.l1 (P2MFourier.phase p) :=
  lt_of_lt_of_le one_pos (ParityDegreeDepth.Core.sign_spectral_bounds p).1

/-- one level of the recursion: a subspace on which the top form vanishes -/
private lemma codim_step (j : ℕ) (hj : 2 ≤ j) (p : Vec n (ZMod 2) → ZMod 2)
    (hp : P2MDiff.DegLe j p) :
    ∃ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ h : Fin j → Fin n → ZMod 2, (∀ i, h i ∈ U) → P2MDiff.diffs p h 0 = 0) ∧
      ((n : ℝ) - Module.finrank (ZMod 2) U) ≤
        Gam j * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := by
  by_cases hj2 : j = 2
  · subst hj2
    obtain ⟨U, h1, h2⟩ := ParityDegreeDepth.Core.quadratic_vanishing_codim p hp
    refine ⟨U, h1, ?_⟩
    simp only [Gam, if_true, one_mul]
    exact h2
  · obtain ⟨U, h1, h2⟩ := ParityDegreeDepth.Core.top_form_vanishing_codim (j := j) (by omega) p hp
    refine ⟨U, h1, ?_⟩
    unfold Gam; rw [if_neg hj2]; exact h2

/-- the recursion over the degree (Lemma 3.1 with `Γ(2) = log‖f̂‖₁`, `Γ(j) = 2^{2j-3} log‖f̂‖₁`) -/
private theorem rec_tree : ∀ d, 1 ≤ d → ∀ (n : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
    P2MDiff.DegLe d p → ∃ t : ParityTree n, (∀ x, treeEval t x = phase p x) ∧
      (treeDepth t : ℝ) ≤ 1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro n p hp
    obtain ⟨t, ht, htf⟩ := affine_tree p hp
    refine ⟨t, htf, ?_⟩
    rw [Gs_one, zero_mul, add_zero]
    exact_mod_cast ht
  | succ d hd ih =>
    intro n p hp
    classical
    obtain ⟨U, hUv, hUc⟩ := codim_step (d+1) (by omega) p hp
    set m := Module.finrank (ZMod 2) U
    let bU := Module.finBasis (ZMod 2) U
    let B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      U.subtype ∘ₗ bU.equivFun.symm.toLinearMap
    have hBinj : Function.Injective B := by
      intro y y' h
      have := Subtype.ext h
      exact bU.equivFun.symm.injective this
    have hBU : ∀ y, B y ∈ U := fun y => (bU.equivFun.symm y).2
    have hUB : ∀ u ∈ U, ∃ y, B y = u := by
      intro u hu
      exact ⟨bU.equivFun ⟨u, hu⟩, by simp [B]⟩
    -- trees on the cosets
    have hcell : ∀ a : Fin n → ZMod 2, ∃ t' : ParityTree n,
        (∀ y, treeEval t' (a + B y) = phase p (a + B y)) ∧
        (treeDepth t' : ℝ) ≤ 1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := by
      intro a
      let q : Vec m (ZMod 2) → ZMod 2 := fun y => p (a + B y)
      have hq : P2MDiff.DegLe d q := by
        intro h y
        show P2MDiff.diffs (fun y => p (a + B y)) h y = 0
        rw [P2MDiff.diffs_comp, P2MDiff.diffs_const hp]
        exact hUv _ (fun i => hBU _)
      obtain ⟨t, htf, htd⟩ := ih m q hq
      obtain ⟨t', ht'd, ht'⟩ := transport B hBinj a t
      refine ⟨t', fun y => by rw [ht', htf]; rfl, ?_⟩
      rw [ht'd]
      refine htd.trans ?_
      have hl1 : P2MFourier.l1 (P2MFourier.phase q) ≤ P2MFourier.l1 (P2MFourier.phase p) :=
        ParityDegreeDepth.Core.spectral_norm_affine_restriction (P2MFourier.phase p) B a
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (l1_pos q) hl1
      have := Gs_nonneg d
      nlinarith
    choose tf htf htfd using hcell
    -- parity checks cutting out the cosets of U
    let Q := (Fin n → ZMod 2) ⧸ U
    let bQ := Module.finBasis (ZMod 2) Q
    set k := Module.finrank (ZMod 2) Q
    let φ : Fin k → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      fun i => (LinearMap.proj i) ∘ₗ bQ.equivFun.toLinearMap ∘ₗ U.mkQ
    let cs : Fin k → Fin n → ZMod 2 := fun i j => φ i (Pi.single j 1)
    have hcs : ∀ i x, cs i ⬝ᵥ x = φ i x := by
      intro i x
      have := P2MDiff.additive_expand (φ i) (fun u v => map_add _ u v) x
      rw [this, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hmemU : ∀ x, (∀ i, cs i ⬝ᵥ x = 0) → x ∈ U := by
      intro x hx
      have h0 : bQ.equivFun (U.mkQ x) = 0 := by
        funext i; have := hx i; rw [hcs] at this; exact this
      have : U.mkQ x = 0 := bQ.equivFun.injective (by rw [h0, map_zero])
      exact (Submodule.Quotient.mk_eq_zero U).mp this
    have hk : (k : ℝ) = (n : ℝ) - m := by
      have := Submodule.finrank_quotient_add_finrank U
      simp only [Module.finrank_fin_fun] at this
      have : (k : ℝ) + m = n := by exact_mod_cast this
      linarith
    set D := Finset.univ.sup fun a => treeDepth (tf a)
    obtain ⟨t, htd, htS⟩ := coset_tree (phase p) D tf (List.ofFn cs) Set.univ (by
      intro a _
      refine ⟨Finset.le_sup (f := fun a => treeDepth (tf a)) (Finset.mem_univ a), ?_⟩
      intro x _ hx
      have hxa : x + a ∈ U := by
        apply hmemU
        intro i
        have := hx (cs i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
        rw [dotProduct_add, this]
        exact CharTwo.add_self_eq_zero _
      obtain ⟨y, hy⟩ := hUB _ hxa
      have hx' : x = a + B y := by
        rw [hy, add_comm x a, ← add_assoc, P2MFourier.pself a, zero_add]
      rw [hx']; exact htf a y)
    refine ⟨t, fun x => htS x (Set.mem_univ x), ?_⟩
    have hD : (D : ℝ) ≤ 1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := by
      obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun a => treeDepth (tf a))
      rw [show D = treeDepth (tf a) from ha]
      exact htfd a
    have hlen : ((List.ofFn cs).length : ℝ) = k := by simp
    have : (treeDepth t : ℝ) ≤ (List.ofFn cs).length + D := by exact_mod_cast htd
    rw [Gs_succ hd]
    calc (treeDepth t : ℝ) ≤ (List.ofFn cs).length + D := this
      _ ≤ Gam (d+1) * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) +
          (1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p))) := by
          rw [hlen, hk]; exact add_le_add hUc hD
      _ = _ := by ring

end rec

section final

variable {n : ℕ}

private def sim : ParityTree n → DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2))
  | .leaf b => .leaf b
  | .query a _ l r => .alice (fun x => decide (a ⬝ᵥ x = 1))
      (.bob (fun y => decide (a ⬝ᵥ y = 1)) (sim l) (sim r))
      (.bob (fun y => decide (a ⬝ᵥ y = 1)) (sim r) (sim l))

private lemma sim_sign : ∀ (t : ParityTree n) (x y : Vec n (ZMod 2)),
    protocolSign (sim t) x y = treeEval t (x + y) := by
  intro t
  induction t with
  | leaf b => intro x y; rfl
  | query a ha l r ihl ihr =>
    intro x y
    have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    simp only [protocolSign, sim, DetCCHard.Protocol.eval] at ihl ihr ⊢
    rw [treeEval_query, dotProduct_add]
    rcases h01 (a ⬝ᵥ x) with hx | hx <;> rcases h01 (a ⬝ᵥ y) with hy | hy <;>
      simp only [hx, hy, decide_true, decide_false, if_true, if_false, Bool.false_eq_true,
        zero_ne_one, one_ne_zero, ihl, ihr] <;> first | rfl | (simp; done) | skip
    all_goals
      first
      | (rw [if_pos (by decide)]; exact ihl x y)
      | (rw [if_neg (by decide)]; exact ihr x y)

private lemma sim_depth : ∀ t : ParityTree n, (sim t).depth = 2 * treeDepth t := by
  intro t
  induction t with
  | leaf b => rfl
  | query a ha l r ihl ihr =>
    simp only [sim, DetCCHard.Protocol.depth, treeDepth, ihl, ihr]
    omega

private theorem main_result :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
    2 ≤ d → anfDegree p = (d : WithBot ℕ) →
    (parityDepth (phase p) : ℝ) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ∧
    1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    communicationDepth (phase p) ≤ 2 * parityDepth (phase p) ∧
    (parityDepth (phase p) : ℝ) ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) := by
  refine ⟨1, one_pos, ?_⟩
  intro n d p hd hp
  classical
  -- degree information
  have hcoef : ∀ S : Finset (Fin n), d < S.card → coefficient p S = 0 := by
    intro S hS
    by_contra hne
    have : ((S.card : ℕ) : WithBot ℕ) ≤ anfDegree p := by
      unfold anfDegree
      refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun S : Finset (Fin n) =>
        if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ)) (Finset.mem_univ S))
      simp only [if_neg hne]
    rw [hp] at this
    have : S.card ≤ d := by exact_mod_cast this
    omega
  have hdeg : P2MDiff.DegLe d p := (ParityDegreeDepth.Core.anf_degree_differences p).1 hcoef
  have hnaff : ¬ ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0 := by
    intro haff
    obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset (Fin n)))
      Finset.univ_nonempty (fun S : Finset (Fin n) =>
        if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ))
    have h1 : anfDegree p = if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ) :=
      hS
    rw [hp] at h1
    split_ifs at h1 with hc
    · exact WithBot.natCast_ne_bot d h1
    · have hcard : d = S.card := by exact_mod_cast h1
      exact hc ((ParityDegreeDepth.Core.anf_degree_differences (d := d) p).2 haff S (by omega))
  have hsp : 2 ≤ sparsity (phase p) := by
    by_contra hlt
    exact hnaff ((ParityDegreeDepth.Core.sign_spectral_bounds p).2.2
      (Nat.lt_succ_iff.mp (not_le.mp hlt)))
  -- the tree
  obtain ⟨t, ht, htd⟩ := rec_tree d (by omega) n p hdeg
  have hPD : parityDepth (phase p) ≤ treeDepth t := Nat.sInf_le ⟨t, rfl, ht⟩
  set L1 := spectralNorm (phase p) with hL1
  set sp := sparsity (phase p) with hsp_def
  have hL1eq : L1 = P2MFourier.l1 (P2MFourier.phase p) := rfl
  have hL1pos : 0 < L1 := l1_pos p
  set a : ℝ := (2 : ℝ) ^ (2 * d - 1) - 5 with ha
  have ha0 : 0 ≤ a := by
    have : (2 : ℝ) ^ 3 ≤ 2 ^ (2 * d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  have hlogT : ∀ x, logTwo x = Real.logb 2 x := fun x => rfl
  have h1 : (parityDepth (phase p) : ℝ) ≤ 1 + a / 3 * logTwo L1 := by
    rw [hlogT]
    have := Gs_closed d hd
    calc (parityDepth (phase p) : ℝ) ≤ treeDepth t := by exact_mod_cast hPD
      _ ≤ 1 + Gs d * Real.logb 2 (P2MFourier.l1 (P2MFourier.phase p)) := htd
      _ = 1 + a / 3 * Real.logb 2 L1 := by rw [this, hL1eq]
  have hsq : L1 ^ 2 ≤ sp := (ParityDegreeDepth.Core.sign_spectral_bounds p).2.1
  have hsppos : (0 : ℝ) < sp := by
    have : (2 : ℝ) ≤ sp := by exact_mod_cast hsp
    linarith
  have hlogL : 2 * logTwo L1 ≤ logTwo sp := by
    rw [hlogT, hlogT]
    calc 2 * Real.logb 2 L1 = Real.logb 2 (L1 ^ 2) := by rw [Real.logb_pow]; push_cast; ring
      _ ≤ Real.logb 2 sp := Real.logb_le_logb_of_le (by norm_num) (by positivity) hsq
  have h2 : 1 + a / 3 * logTwo L1 ≤ 1 + a / 6 * logTwo sp := by
    have : a / 3 * logTwo L1 ≤ a / 6 * logTwo sp := by
      have := mul_le_mul_of_nonneg_left hlogL ha0
      linarith
    linarith
  -- communication
  obtain ⟨t0, ht0d, ht0⟩ : ∃ t0 : ParityTree n, treeDepth t0 = parityDepth (phase p) ∧
      ∀ x, treeEval t0 x = phase p x :=
    Nat.sInf_mem (s := {k | ∃ t : ParityTree n, treeDepth t = k ∧ ∀ x, treeEval t x = phase p x})
      ⟨_, t, rfl, ht⟩
  have h4 : communicationDepth (phase p) ≤ 2 * parityDepth (phase p) := by
    rw [← ht0d, ← sim_depth]
    exact Nat.sInf_le ⟨sim t0, rfl, fun x y => by rw [sim_sign, ht0]⟩
  have h4r : (communicationDepth (phase p) : ℝ) / 2 ≤ parityDepth (phase p) := by
    have : (communicationDepth (phase p) : ℝ) ≤ 2 * parityDepth (phase p) := by exact_mod_cast h4
    linarith
  -- uniform constant
  have hlogs : 1 ≤ logTwo sp := by
    rw [hlogT]
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ) < 2)
      (show (2:ℝ) ≤ sp by exact_mod_cast hsp)
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have h5 : (parityDepth (phase p) : ℝ) ≤ 1 * (4 : ℝ) ^ d * logTwo sp := by
    have h4d : (4 : ℝ) ^ d = 2 * 2 ^ (2 * d - 1) := by
      have e : (2:ℝ) ^ (2 * d) = 2 ^ (2 * d - 1 + 1) := by congr 1; omega
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, e, pow_succ]; ring
    have h16 : (16 : ℝ) ≤ 4 ^ d := by
      have : (4 : ℝ) ^ 2 ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) hd
      norm_num at this; linarith
    have hpow : (8 : ℝ) ≤ 2 ^ (2 * d - 1) := by
      have : (2 : ℝ) ^ 3 ≤ 2 ^ (2 * d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    calc (parityDepth (phase p) : ℝ) ≤ 1 + a / 6 * logTwo sp := h1.trans h2
      _ ≤ 1 * (4 : ℝ) ^ d * logTwo sp := by
        rw [h4d, ha]
        nlinarith
  refine ⟨h1, h2, ?_, h4, h5, ?_⟩
  · exact h4r.trans (h1.trans h2)
  · exact h4r.trans h5

end final

end ParityDegreeDepth.Main

open ParityDegreeDepth.Core.Setting in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
    2 ≤ d → anfDegree p = (d : WithBot ℕ) →
    (parityDepth (phase p) : ℝ) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ∧
    1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    communicationDepth (phase p) ≤ 2 * parityDepth (phase p) ∧
    (parityDepth (phase p) : ℝ) ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) := ParityDegreeDepth.Main.main_result
