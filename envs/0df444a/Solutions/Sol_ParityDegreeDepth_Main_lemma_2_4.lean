-- Prove2me | solution 1 for ParityDegreeDepth.Main.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:34:43.600268+00:00
-- url     : https://prove2.me/submissions/7ebe713f-aac0-46bb-bef0-c3cd52af9c81

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_ParityDegreeDepth_Core_tensorEval
import Theorems.Thm_ParityDegreeDepth_Core_anf_degree_differences

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

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

private def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

private def delta {n : ℕ} (h : Vec n (ZMod 2)) (p : Vec n (ZMod 2) → ZMod 2)
    (x : Vec n (ZMod 2)) : ZMod 2 := p (x + h) + p x

private def differences {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v => delta v q) p

private abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

private def topForm {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (d : ℕ) : Form (ZMod 2) n d :=
  fun h => differences p h 0

private def Vanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop := ∀ x, (∀ i, x i ∈ U) → T x = 0




/-- ANF degree at most `k` gives vanishing `(k+1)`-fold differences -/
private lemma degLe_of_anf_le {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hp : anfDegree p ≤ (k : WithBot ℕ)) : P2MDiff.DegLe k p := by
  classical
  apply (ParityDegreeDepth.Core.anf_degree_differences (d := k) p).1
  intro S hS
  by_contra hne
  have : ((S.card : ℕ) : WithBot ℕ) ≤ anfDegree p := by
    unfold anfDegree
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun S : Finset (Fin n) =>
      if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ)) (Finset.mem_univ S))
    simp only [show coefficient p S = (if ParityCubes.anfCoeff
      (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S then (1 : ZMod 2) else 0) from rfl,
      if_neg hne]
  have := this.trans hp
  have : S.card ≤ k := by exact_mod_cast this
  omega

private lemma coeff_eq_top {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (ind : Fin d → Fin n)
    (hind : Function.Injective ind) :
    P2MDiff.diffs p (fun i => Pi.single (ind i) 1) 0 = coefficient p (Finset.univ.image ind) := by
  classical
  rw [show coefficient p (Finset.univ.image ind) = P2MANF.coeffZ p (Finset.univ.image ind) from rfl,
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


private lemma diffs_vanish_of_degLe {n k N : ℕ} {q : Vec n (ZMod 2) → ZMod 2} (hq : P2MDiff.DegLe k q)
    (hN : k < N) (h : Fin N → Vec n (ZMod 2)) (x : Vec n (ZMod 2)) : P2MDiff.diffs q h x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  exact P2MANF.degLe_mono (by omega) hq h x

/-- vanishing `(k+1)`-fold differences give ANF degree at most `k` -/
private lemma anf_le_of_degLe {n k : ℕ} (q : Vec n (ZMod 2) → ZMod 2) (hq : P2MDiff.DegLe k q) :
    anfDegree q ≤ (k : WithBot ℕ) := by
  classical
  unfold anfDegree
  apply Finset.sup_le
  intro S _
  split_ifs with hc
  · exact bot_le
  · by_contra hlt
    have hk : k < S.card := by
      by_contra h'; apply hlt; exact_mod_cast (not_lt.mp h')
    apply hc
    let e := S.equivFin
    let ind : Fin S.card → Fin n := fun i => (e.symm i : Fin n)
    have hind : Function.Injective ind := by
      intro a b hab; exact e.symm.injective (Subtype.ext hab)
    have himg : Finset.univ.image ind = S := by
      ext v; constructor
      · intro hv; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv; exact (e.symm _).2
      · intro hv; exact Finset.mem_image.mpr ⟨e ⟨v, hv⟩, Finset.mem_univ _, by simp [ind]⟩
    rw [← himg, ← coeff_eq_top q ind hind]
    exact diffs_vanish_of_degLe hq hk _ 0

end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- lemma 2 4; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 1 ≤ d) (hp : anfDegree p = (d : WithBot ℕ))
    (U : Submodule (ZMod 2) (Vec n (ZMod 2))) :
    Vanishes (topForm p d) U ↔
    ∀ (a : Vec n (ZMod 2)) (m : ℕ) (B : Vec m (ZMod 2) ≃ₗ[ZMod 2] U),
      anfDegree (fun y => p (a + (B y : Vec n (ZMod 2)))) ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have hdeg : P2MDiff.DegLe (k + 1) p := degLe_of_anf_le p (le_of_eq hp)
  simp only [Nat.add_sub_cancel]
  constructor
  · intro hvan a m B
    apply anf_le_of_degLe
    intro h y
    let B' : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2) := U.subtype ∘ₗ B.toLinearMap
    show P2MDiff.diffs (fun y => p (a + B' y)) h y = 0
    rw [P2MDiff.diffs_comp, P2MDiff.diffs_const hdeg]
    exact hvan _ (fun i => (B (h i)).2)
  · intro H x hx
    let m := Module.finrank (ZMod 2) U
    let B : Vec m (ZMod 2) ≃ₗ[ZMod 2] U := (Module.finBasis (ZMod 2) U).equivFun.symm
    have hq := degLe_of_anf_le _ (H 0 m B)
    let B' : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2) := U.subtype ∘ₗ B.toLinearMap
    let y : Fin (k + 1) → Vec m (ZMod 2) := fun i => B.symm ⟨x i, hx i⟩
    have hxy : x = fun i => B' (y i) := by
      funext i; simp [B', y]
    have := hq y 0
    have e := P2MDiff.diffs_comp p B' 0 y 0
    simp only [map_zero, add_zero] at e
    show P2MDiff.diffs p x 0 = 0
    rw [hxy, ← e]
    exact this



