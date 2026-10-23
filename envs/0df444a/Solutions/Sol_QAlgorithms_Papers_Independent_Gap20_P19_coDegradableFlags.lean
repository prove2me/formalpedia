-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.coDegradableFlags
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:43:59.110883+00:00
-- url     : https://prove2.me/submissions/8c41c631-6aea-47b5-a2ec-cd7a6a1ab3c5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

attribute [local instance] Classical.propDecidable Classical.decEq

open Matrix

lemma x8_finrank_prod {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [FiniteDimensional ℂ M] [FiniteDimensional ℂ N] (p : Submodule ℂ M) (q : Submodule ℂ N) :
    Module.finrank ℂ (p.prod q) = Module.finrank ℂ p + Module.finrank ℂ q := by
  rw [← Module.finrank_prod]
  exact LinearEquiv.finrank_eq
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

/-- rank of a block diagonal matrix -/
lemma x8_rank_blocks {m n : Type} [Fintype m] [Fintype n] (P : Matrix m m ℂ) (Q : Matrix n n ℂ) :
    (fromBlocks P 0 0 Q).rank = P.rank + Q.rank := by
  unfold Matrix.rank
  have e : (fromBlocks P 0 0 Q).mulVecLin =
      (LinearEquiv.sumArrowLequivProdArrow m n ℂ ℂ).symm.toLinearMap ∘ₗ
        (P.mulVecLin.prodMap Q.mulVecLin) ∘ₗ (LinearEquiv.sumArrowLequivProdArrow m n ℂ ℂ).toLinearMap := by
    apply LinearMap.ext; intro v; funext i
    rcases i with i | i <;>
      simp [fromBlocks_mulVec, Function.comp_def] <;> rfl
  rw [e, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    LinearMap.range_prodMap]
  rw [LinearEquiv.finrank_map_eq, x8_finrank_prod]

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def x8e : (A × B) ⊕ (A × B) ≃ A × (Bool × B) where
  toFun := Sum.elim (fun x => (x.1, (false, x.2))) (fun x => (x.1, (true, x.2)))
  invFun := fun y => if y.2.1 then Sum.inr (y.1, y.2.2) else Sum.inl (y.1, y.2.2)
  left_inv := by intro x; rcases x with x | x <;> simp
  right_inv := by
    rintro ⟨a, t, b⟩
    cases t <;> simp

lemma x8_choi_rank (M N : QAlgorithms.Superop A B) :
    (choi (coFlags M N)).rank = (choi M).rank + (choi N).rank := by
  have h : (choi (coFlags M N)).submatrix x8e x8e =
      fromBlocks ((1 / 2 : ℂ) • choi M) 0 0 ((1 / 2 : ℂ) • choi N) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [x8e, choi, coFlags, fromBlocks]
  rw [← rank_submatrix (choi (coFlags M N)) x8e x8e, h, x8_rank_blocks,
    rank_smul_of_mem_nonZeroDivisors, rank_smul_of_mem_nonZeroDivisors] <;>
    exact mem_nonZeroDivisors_of_ne_zero (by norm_num)

variable {E F : Type} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

lemma x8_ent {R : Type} [Fintype R] (M : Matrix R A ℂ) (ρ : Matrix A A ℂ) (r r' : R) :
    (M * ρ * Mᴴ) r r' = ∑ a, ∑ a', M r a * ρ a a' * conj (M r' a') := by
  rw [mul_apply]
  simp only [mul_apply, Finset.sum_mul, conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]

lemma x8_s (x y z : ℂ) :
    ((Real.sqrt 2)⁻¹ : ℂ) * x * y * conj (((Real.sqrt 2)⁻¹ : ℂ) * z) = 1 / 2 * (x * y * conj z) := by
  have h : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [map_mul, map_inv₀, Complex.conj_ofReal]
  linear_combination (x * y * conj z) * h

lemma x8_s' (x y z : ℂ) :
    ((Real.sqrt 2 : ℂ))⁻¹ * x * y * (((Real.sqrt 2 : ℂ))⁻¹ * z) = 2⁻¹ * (x * y * z) := by
  have h : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  linear_combination (x * y * z) * h

lemma x8_recv (U : Matrix (B × E) A ℂ) (V : Matrix (B × F) A ℂ) :
    receiverChannel (coFlagDilation U V) = coFlags (receiverChannel U) (receiverChannel V) := by
  funext ρ; ext ⟨t, b⟩ ⟨t', b'⟩
  simp only [receiverChannel, QAlgorithms.traceRight, coFlags, of_apply, Fintype.sum_sum_type, x8_ent]
  cases t <;> cases t' <;> simp [coFlagDilation, x8_s', ← Finset.mul_sum]

lemma x8_iso (U : Matrix (B × E) A ℂ) (V : Matrix (B × F) A ℂ) (hU : IsIsometry U)
    (hV : IsIsometry V) : IsIsometry (coFlagDilation U V) := by
  unfold IsIsometry at *
  ext a a'
  have hU' := congrFun (congrFun hU a) a'
  have hV' := congrFun (congrFun hV a) a'
  simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
    Fintype.sum_bool] at hU' hV' ⊢
  simp only [coFlagDilation, if_true, if_false, Bool.false_eq_true, star_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, star_mul', Complex.star_def, map_inv₀,
    Complex.conj_ofReal]
  have h : ∀ x y : ℂ, ((Real.sqrt 2 : ℂ))⁻¹ * x * (((Real.sqrt 2 : ℂ))⁻¹ * y) = 2⁻¹ * (x * y) := by
    intro x y
    have h : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    linear_combination (x * y) * h
  simp only [h, ← Finset.mul_sum]
  simp only [Complex.star_def] at hU' hV'
  rw [hU', hV']; ring

lemma x8_comp (U : Matrix (B × E) A ℂ) (V : Matrix (B × F) A ℂ) (ρ : Matrix A A ℂ) :
    (∀ e e', complementaryChannel (coFlagDilation U V) ρ (Sum.inl e) (Sum.inl e') =
      (1 / 2 : ℂ) * complementaryChannel U ρ e e') ∧
    (∀ f f', complementaryChannel (coFlagDilation U V) ρ (Sum.inr f) (Sum.inr f') =
      (1 / 2 : ℂ) * complementaryChannel V ρ f f') ∧
    (∀ e f, complementaryChannel (coFlagDilation U V) ρ (Sum.inl e) (Sum.inr f) = 0) ∧
    (∀ e f, complementaryChannel (coFlagDilation U V) ρ (Sum.inr f) (Sum.inl e) = 0) := by
  refine ⟨fun e e' => ?_, fun f f' => ?_, fun e f => ?_, fun e f => ?_⟩ <;>
  simp [complementaryChannel, QAlgorithms.traceLeft, x8_ent, Fintype.sum_prod_type,
    coFlagDilation, x8_s', ← Finset.mul_sum]

def x8KX {m : ℕ} (EX : Fin m → Matrix E B ℂ) : Fin m → Matrix (E ⊕ F) (Bool × B) ℂ :=
  fun i x r => match x with
    | .inl e => if r.1 then EX i e r.2 else 0
    | .inr _ => 0

def x8KY {m : ℕ} (EY : Fin m → Matrix F B ℂ) : Fin m → Matrix (E ⊕ F) (Bool × B) ℂ :=
  fun i x r => match x with
    | .inl _ => 0
    | .inr f => if r.1 then 0 else EY i f r.2

def x8blk (t : Bool) (σ : Matrix (Bool × B) (Bool × B) ℂ) : Matrix B B ℂ :=
  fun b b' => σ (t, b) (t, b')

lemma x8_kraus {m1 m2 : ℕ} (EX : Fin m1 → Matrix E B ℂ) (EY : Fin m2 → Matrix F B ℂ)
    (hX : QAlgorithms.IsKrausFamily EX) (hY : QAlgorithms.IsKrausFamily EY) :
    QAlgorithms.IsKrausFamily (Fin.append (x8KX (F := F) EX) (x8KY (E := E) EY)) := by
  unfold QAlgorithms.IsKrausFamily at *
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ext ⟨t, b⟩ ⟨t', b'⟩
  have hX' := congrFun (congrFun hX b) b'
  have hY' := congrFun (congrFun hY b) b'
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply] at hX' hY'
  simp only [Matrix.add_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply, Fintype.sum_sum_type,
    x8KX, x8KY]
  simp only [Complex.star_def, Matrix.one_apply] at hX' hY'
  cases t <;> cases t' <;> simp [hX', hY', Matrix.one_apply]

lemma x8_kapp {m1 m2 : ℕ} (EX : Fin m1 → Matrix E B ℂ) (EY : Fin m2 → Matrix F B ℂ)
    (σ : Matrix (Bool × B) (Bool × B) ℂ) :
    (∀ e e', QAlgorithms.krausApply (Fin.append (x8KX (F := F) EX) (x8KY (E := E) EY)) σ
        (Sum.inl e) (Sum.inl e') = QAlgorithms.krausApply EX (x8blk true σ) e e') ∧
    (∀ f f', QAlgorithms.krausApply (Fin.append (x8KX (F := F) EX) (x8KY (E := E) EY)) σ
        (Sum.inr f) (Sum.inr f') = QAlgorithms.krausApply EY (x8blk false σ) f f') ∧
    (∀ e f, QAlgorithms.krausApply (Fin.append (x8KX (F := F) EX) (x8KY (E := E) EY)) σ
        (Sum.inl e) (Sum.inr f) = 0) ∧
    (∀ e f, QAlgorithms.krausApply (Fin.append (x8KX (F := F) EX) (x8KY (E := E) EY)) σ
        (Sum.inr f) (Sum.inl e) = 0) := by
  refine ⟨fun e e' => ?_, fun f f' => ?_, fun e f => ?_, fun e f => ?_⟩ <;>
  simp [QAlgorithms.krausApply, Fin.sum_univ_add, Matrix.sum_apply, x8_ent, Fintype.sum_prod_type,
    x8KX, x8KY, x8blk]

lemma x8_kr_smul {K ι κ : Type} [Fintype K] [Fintype ι] (EE : K → Matrix κ ι ℂ) (c : ℂ)
    (M : Matrix ι ι ℂ) : QAlgorithms.krausApply EE (c • M) = c • QAlgorithms.krausApply EE M := by
  simp [QAlgorithms.krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma x8_degr (U : Matrix (B × E) A ℂ) (V : Matrix (B × F) A ℂ)
    (hU : IsIsometry U) (hV : IsIsometry V)
    (X : QAlgorithms.Superop B E) (Y : QAlgorithms.Superop B F)
    (hX : QAlgorithms.IsChannel X) (hY : QAlgorithms.IsChannel Y)
    (hcrossX : ∀ rho, X (receiverChannel V rho) = complementaryChannel U rho)
    (hcrossY : ∀ rho, Y (receiverChannel U rho) = complementaryChannel V rho) :
    IsDegradable (coFlagDilation U V) := by
  obtain ⟨m1, EX, hEX, hXk⟩ := hX
  obtain ⟨m2, EY, hEY, hYk⟩ := hY
  refine ⟨x8_iso U V hU hV, QAlgorithms.krausApply (Fin.append (x8KX (F := F) EX) (x8KY (E := E) EY)),
    ⟨m1 + m2, _, x8_kraus EX EY hEX hEY, fun ρ => rfl⟩, fun ρ => ?_⟩
  have hb1 : x8blk true (receiverChannel (coFlagDilation U V) ρ) =
      (1 / 2 : ℂ) • receiverChannel V ρ := by
    rw [x8_recv]; ext b b'; simp [x8blk, coFlags]
  have hb2 : x8blk false (receiverChannel (coFlagDilation U V) ρ) =
      (1 / 2 : ℂ) • receiverChannel U ρ := by
    rw [x8_recv]; ext b b'; simp [x8blk, coFlags]
  obtain ⟨c1, c2, c3, c4⟩ := x8_comp U V ρ
  obtain ⟨k1, k2, k3, k4⟩ := x8_kapp EX EY (receiverChannel (coFlagDilation U V) ρ)
  ext x y
  rcases x with e | f <;> rcases y with e' | f'
  · rw [c1, k1, hb1, x8_kr_smul, ← hXk, hcrossX]; rfl
  · rw [c3, k3]
  · rw [c4, k4]
  · rw [c2, k2, hb2, x8_kr_smul, ← hYk, hcrossY]; rfl

lemma x8_main [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty F]
    (U : Matrix (B × E) A ℂ) (V : Matrix (B × F) A ℂ)
    (hU : IsIsometry U) (hV : IsIsometry V)
    (X : QAlgorithms.Superop B E) (Y : QAlgorithms.Superop B F)
    (hX : QAlgorithms.IsChannel X) (hY : QAlgorithms.IsChannel Y)
    (hcrossX : ∀ rho, X (receiverChannel V rho) = complementaryChannel U rho)
    (hcrossY : ∀ rho, Y (receiverChannel U rho) = complementaryChannel V rho) :
    receiverChannel (coFlagDilation U V) = coFlags (receiverChannel U) (receiverChannel V) ∧
    IsDegradable (coFlagDilation U V) ∧
    (choi (coFlags (receiverChannel U) (receiverChannel V))).rank =
      (choi (receiverChannel U)).rank+(choi (receiverChannel V)).rank :=
  ⟨x8_recv U V, x8_degr U V hU hV X Y hX hY hcrossX hcrossY, x8_choi_rank _ _⟩

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
/-- Section 2.3, PDF p.11, (24)–(25): cross-degraders are hypotheses on
the pair; their environments remain distinct. Minimal Kraus ranks add. -/
theorem solution [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty F]
    (U : Matrix (B × E) A ℂ) (V : Matrix (B × F) A ℂ)
    (hU : IsIsometry U) (hV : IsIsometry V)
    (X : Superop B E) (Y : Superop B F) (hX : IsChannel X) (hY : IsChannel Y)
    (hcrossX : ∀ rho, X (receiverChannel V rho) = complementaryChannel U rho)
    (hcrossY : ∀ rho, Y (receiverChannel U rho) = complementaryChannel V rho) :
    receiverChannel (coFlagDilation U V) = coFlags (receiverChannel U) (receiverChannel V) ∧
    IsDegradable (coFlagDilation U V) ∧
    (choi (coFlags (receiverChannel U) (receiverChannel V))).rank =
      (choi (receiverChannel U)).rank+(choi (receiverChannel V)).rank :=
  x8_main U V hU hV X Y hX hY hcrossX hcrossY



