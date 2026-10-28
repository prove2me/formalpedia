-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.example12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:48:26.055285+00:00
-- url     : https://prove2.me/submissions/0ff7b6ba-32f0-41af-9c7d-77afd3edc619

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section S200X

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type*} [Field F] {m : ℕ}

def S200X_good (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) : Prop :=
  (∀ i j, X (Sum.inr i) j = 0) ∧ ∑ i, X (Sum.inl i) (Sum.inl i) = 0

theorem S200X_good_iff (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    S200X_good X ↔ ∃ C D : Matrix (Fin m) (Fin m) F,
      Matrix.trace C = 0 ∧ X = blockElement m C D := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨X.toBlocks₁₁, X.toBlocks₁₂, h2, ?_⟩
    ext (i|i) (j|j) <;> simp [blockElement, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, h1]
  · rintro ⟨C, D, hC, rfl⟩
    refine ⟨?_, ?_⟩
    · intro i j; rcases j with j|j <;> simp [blockElement]
    · simpa [blockElement, Matrix.trace] using hC

def S200X_T (F : Type*) [Field F] (m : ℕ) :
    LieSubalgebra F (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) where
  carrier := {X | S200X_good X}
  add_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    exact ⟨fun i j => by simp [hX1, hY1], by simp [Finset.sum_add_distrib, hX2, hY2]⟩
  zero_mem' := ⟨fun _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro c X ⟨hX1, hX2⟩
    exact ⟨fun i j => by simp [hX1], by simp [← Finset.mul_sum, hX2]⟩
  lie_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    refine ⟨fun i j => ?_, ?_⟩
    · simp [Ring.lie_def, Matrix.mul_apply, hX1, hY1]
    · simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_sum_type, hX1, hY1,
        mul_zero, Finset.sum_const_zero, add_zero, Finset.sum_sub_distrib]
      rw [sub_eq_zero, Finset.sum_comm]
      simp only [mul_comm]

theorem S200X_span_eq :
    bahturinBlockLieAlgebra F m = S200X_T F m := by
  unfold bahturinBlockLieAlgebra
  have : {X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F |
      ∃ C D : Matrix (Fin m) (Fin m) F, Matrix.trace C = 0 ∧ X = blockElement m C D} =
      (S200X_T F m : Set _) := by
    ext X; exact (S200X_good_iff X).symm
  rw [this, LieSubalgebra.lieSpan_eq]

theorem S200X_memL (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    X ∈ bahturinBlockLieAlgebra F m ↔ S200X_good X := by
  rw [S200X_span_eq]; rfl

theorem S200X_low (x : bahturinBlockLieAlgebra F m) (i : Fin m) (j : Fin m ⊕ Fin m) :
    (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (Sum.inr i) j = 0 :=
  ((S200X_memL _).1 x.2).1 i j

theorem S200X_tr (x : bahturinBlockLieAlgebra F m) :
    ∑ i, (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (Sum.inl i) (Sum.inl i) = 0 :=
  ((S200X_memL _).1 x.2).2

def S200X_Z (F : Type*) [Field F] (m : ℕ) :
    Submodule F (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) where
  carrier := {X | (∀ i j, X (Sum.inl i) (Sum.inl j) = 0) ∧ ∀ i j, X (Sum.inr i) j = 0}
  add_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    exact ⟨fun i j => by simp [hX1, hY1], fun i j => by simp [hX2, hY2]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c X ⟨hX1, hX2⟩
    exact ⟨fun i j => by simp [hX1], fun i j => by simp [hX2]⟩

theorem S200X_spanZ :
    Submodule.span F {X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F |
      ∃ D : Matrix (Fin m) (Fin m) F, X = blockElement m 0 D} = S200X_Z F m := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro X ⟨D, rfl⟩
    refine ⟨fun i j => by simp [blockElement], fun i j => ?_⟩
    rcases j with j|j <;> simp [blockElement]
  · rintro X ⟨h1, h2⟩
    apply Submodule.subset_span
    refine ⟨X.toBlocks₁₂, ?_⟩
    ext (i|i) (j|j) <;> simp [blockElement, Matrix.toBlocks₁₂, h1, h2]

theorem S200X_memR (x : bahturinBlockLieAlgebra F m) :
    x ∈ blockRadical F m ↔
      ∀ i j, (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (Sum.inl i) (Sum.inl j) = 0 := by
  unfold blockRadical
  rw [Submodule.mem_comap, S200X_spanZ]
  exact ⟨fun h => h.1, fun h => ⟨h, S200X_low x⟩⟩

theorem S200X_lieval (x y : bahturinBlockLieAlgebra F m) :
    ((⁅x, y⁆ : bahturinBlockLieAlgebra F m) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) =
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) * (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) -
        (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) * (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) := by
  rw [LieSubalgebra.coe_bracket, Ring.lie_def]

def S200X_Rid (F : Type*) [Field F] (m : ℕ) : LieIdeal F (bahturinBlockLieAlgebra F m) :=
  { blockRadical F m with
    lie_mem := by
      intro x y hy
      have hy' := (S200X_memR y).1 hy
      show _ ∈ blockRadical F m
      rw [S200X_memR]
      intro i j
      simp [Ring.lie_def, Matrix.mul_apply, Fintype.sum_sum_type, hy', S200X_low] }

theorem S200X_Rid_sub : (S200X_Rid F m).toSubmodule = blockRadical F m := rfl

instance S200X_Rid_abel : IsLieAbelian (S200X_Rid F m) := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  have hx' := (S200X_memR x).1 hx
  have hy' := (S200X_memR y).1 hy
  apply Subtype.ext; apply Subtype.ext
  change ((⁅x, y⁆ : bahturinBlockLieAlgebra F m) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) = 0
  rw [S200X_lieval]
  ext (i|i) (j|j) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hx', hy', S200X_low]


abbrev S200X_M (F : Type*) [Field F] (m : ℕ) := Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F

theorem S200X_E_mem (a b : Fin m) (hab : a ≠ b) :
    (Matrix.single (Sum.inl a) (Sum.inl b) (1 : F) : S200X_M F m) ∈ bahturinBlockLieAlgebra F m := by
  rw [S200X_memL]
  refine ⟨fun i j => by simp, ?_⟩
  apply Finset.sum_eq_zero
  intro i _
  apply Matrix.single_apply_of_ne
  rintro ⟨h1, h2⟩
  apply hab
  have h1' := Sum.inl.inj h1
  have h2' := Sum.inl.inj h2
  rw [h1', h2']

def S200X_E (a b : Fin m) (hab : a ≠ b) : bahturinBlockLieAlgebra F m :=
  ⟨Matrix.single (Sum.inl a) (Sum.inl b) (1 : F), S200X_E_mem a b hab⟩

theorem S200X_E_val (a b : Fin m) (hab : a ≠ b) :
    ((S200X_E (F := F) a b hab : bahturinBlockLieAlgebra F m) : S200X_M F m) =
      Matrix.single (Sum.inl a) (Sum.inl b) 1 := rfl

theorem S200X_dbl (E X : S200X_M F m) (hE : E * E = 0) :
    E * (E * X - X * E) - (E * X - X * E) * E = -(2 : F) • (E * X * E) := by
  have h1 : E * (E * X) = 0 := by rw [← mul_assoc, hE, zero_mul]
  have h2 : X * E * E = 0 := by rw [mul_assoc, hE, mul_zero]
  simp only [mul_sub, sub_mul, ← mul_assoc, hE, zero_mul, h2]
  rw [neg_smul, two_smul]
  abel

theorem S200X_off [CharZero F] (J : LieIdeal F (bahturinBlockLieAlgebra F m))
    (x : bahturinBlockLieAlgebra F m) (hx : x ∈ J) (i j : Fin m) (hij : i ≠ j)
    (hne : (x : S200X_M F m) (Sum.inl i) (Sum.inl j) ≠ 0) :
    ∃ y ∈ J, (y : S200X_M F m) = Matrix.single (Sum.inl j) (Sum.inl i) 1 := by
  set e := S200X_E (F := F) j i hij.symm
  have hz : ⁅e, ⁅e, x⁆⁆ ∈ J := J.lie_mem (J.lie_mem hx)
  have hEE : (e : S200X_M F m) * e = 0 := by
    rw [S200X_E_val]
    simp [hij]
  have hz' : ((⁅e, ⁅e, x⁆⁆ : bahturinBlockLieAlgebra F m) : S200X_M F m) =
      (-(2 : F) * (x : S200X_M F m) (Sum.inl i) (Sum.inl j)) •
        Matrix.single (Sum.inl j) (Sum.inl i) 1 := by
    rw [S200X_lieval, S200X_lieval, S200X_dbl _ _ hEE, S200X_E_val,
      Matrix.single_mul_mul_single, Matrix.smul_single, smul_eq_mul]
    simp [Matrix.single_neg]
  refine ⟨(-(2 : F) * (x : S200X_M F m) (Sum.inl i) (Sum.inl j))⁻¹ • ⁅e, ⁅e, x⁆⁆,
    J.smul_mem _ hz, ?_⟩
  change _ • ((⁅e, ⁅e, x⁆⁆ : bahturinBlockLieAlgebra F m) : S200X_M F m) = _
  rw [hz', smul_smul, inv_mul_cancel₀, one_smul]
  exact mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hne

theorem S200X_getE [CharZero F] (J : LieIdeal F (bahturinBlockLieAlgebra F m))
    (x : bahturinBlockLieAlgebra F m) (hx : x ∈ J) (hxR : x ∉ blockRadical F m) :
    ∃ a b : Fin m, a ≠ b ∧ ∃ y ∈ J, (y : S200X_M F m) = Matrix.single (Sum.inl a) (Sum.inl b) 1 := by
  by_cases hoff : ∃ i j, i ≠ j ∧ (x : S200X_M F m) (Sum.inl i) (Sum.inl j) ≠ 0
  · obtain ⟨i, j, hij, hne⟩ := hoff
    exact ⟨j, i, hij.symm, S200X_off J x hx i j hij hne⟩
  push Not at hoff
  rw [S200X_memR] at hxR
  push Not at hxR
  obtain ⟨k, k', hk⟩ := hxR
  have hkk : k = k' := by
    by_contra h; exact hk (hoff k k' h)
  subst hkk
  have : ∃ l, (x : S200X_M F m) (Sum.inl l) (Sum.inl l) ≠ (x : S200X_M F m) (Sum.inl k) (Sum.inl k) := by
    by_contra hall
    push Not at hall
    have htr := S200X_tr x
    rw [Finset.sum_congr rfl (fun l _ => hall l), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at htr
    rcases mul_eq_zero.1 htr with h | h
    · have : m = 0 := by exact_mod_cast h
      subst this; exact k.elim0
    · exact hk h
  obtain ⟨l, hl⟩ := this
  have hlk : l ≠ k := by rintro rfl; exact hl rfl
  set e := S200X_E (F := F) l k hlk
  have hz : ⁅e, x⁆ ∈ J := J.lie_mem hx
  have hne : ((⁅e, x⁆ : bahturinBlockLieAlgebra F m) : S200X_M F m) (Sum.inl l) (Sum.inl k) ≠ 0 := by
    rw [S200X_lieval, S200X_E_val, Matrix.sub_apply, Matrix.single_mul_apply_same,
      Matrix.mul_single_apply_same, one_mul, mul_one, sub_ne_zero]
    exact fun h => hl h.symm
  exact ⟨k, l, hlk.symm, S200X_off J _ hz l k hlk hne⟩

theorem S200X_step [CharZero F] (J : LieIdeal F (bahturinBlockLieAlgebra F m))
    (hJ : ¬ J ≤ S200X_Rid F m) : ¬ ⁅J, J⁆ ≤ S200X_Rid F m := by
  rw [SetLike.not_le_iff_exists] at hJ
  obtain ⟨x, hx, hxR⟩ := hJ
  obtain ⟨a, b, hab, y, hy, hyv⟩ := S200X_getE J x hx hxR
  obtain ⟨y', hy', hy'v⟩ := S200X_off J y hy a b hab (by rw [hyv]; simp)
  intro hle
  have hmem := hle (LieSubmodule.lie_mem_lie hy hy')
  have h2 := (S200X_memR _).1 hmem a a
  rw [S200X_lieval, hyv, hy'v, Matrix.sub_apply, Matrix.single_mul_single_same,
    Matrix.single_mul_single_same] at h2
  have h3 : (Matrix.single (Sum.inl b) (Sum.inl b) (1 * 1 : F) : S200X_M F m) (Sum.inl a) (Sum.inl a) = 0 :=
    Matrix.single_apply_of_ne _ _ _ _ _ (by simp [Ne.symm hab])
  rw [h3, Matrix.single_apply_same] at h2
  simp at h2

theorem S200X_solv_le [CharZero F] (I : LieIdeal F (bahturinBlockLieAlgebra F m))
    (hI : LieAlgebra.IsSolvable I) : I ≤ S200X_Rid F m := by
  by_contra h
  have hk : ∀ k, ¬ LieAlgebra.derivedSeriesOfIdeal F _ k I ≤ S200X_Rid F m := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      rw [LieAlgebra.derivedSeriesOfIdeal_succ]
      exact S200X_step _ ih
  obtain ⟨k, hk'⟩ := LieAlgebra.IsSolvable.solvable F I
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hk'
  exact hk k (by rw [hk']; exact bot_le)

theorem S200X_rad [CharZero F] :
    LieAlgebra.radical F (bahturinBlockLieAlgebra F m) = S200X_Rid F m ∧
    lieNilpotentRadical F (bahturinBlockLieAlgebra F m) = S200X_Rid F m := by
  have h1 : LieAlgebra.radical F (bahturinBlockLieAlgebra F m) ≤ S200X_Rid F m :=
    sSup_le fun I hI => S200X_solv_le I hI
  have h2 : lieNilpotentRadical F (bahturinBlockLieAlgebra F m) ≤
      LieAlgebra.radical F (bahturinBlockLieAlgebra F m) :=
    sSup_le_sSup fun I (_ : LieModule.IsNilpotent I I) ↦ LieAlgebra.isSolvable_of_isNilpotent I
  have h3 : S200X_Rid F m ≤ lieNilpotentRadical F (bahturinBlockLieAlgebra F m) :=
    le_sSup (show LieModule.IsNilpotent (S200X_Rid F m) (S200X_Rid F m) from inferInstance)
  exact ⟨le_antisymm h1 (h3.trans h2), le_antisymm (h2.trans h1) h3⟩

def S200X_P (m : ℕ) (n : F) : S200X_M F m :=
  Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) F) (n • 1) 0 1

theorem S200X_xP_inl (X : S200X_M F m) (n : F) (a : Fin m ⊕ Fin m) (j : Fin m) :
    (X * S200X_P m n) a (Sum.inl j) = X a (Sum.inl j) := by
  simp [S200X_P, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem S200X_xP_inr (X : S200X_M F m) (n : F) (a : Fin m ⊕ Fin m) (j : Fin m) :
    (X * S200X_P m n) a (Sum.inr j) = X a (Sum.inr j) + n * X a (Sum.inl j) := by
  simp [S200X_P, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, add_comm, mul_comm]

theorem S200X_Pmul (Y : S200X_M F m) (hY : ∀ i j, Y (Sum.inr i) j = 0) (n : F) :
    S200X_P m n * Y = Y := by
  ext (i|i) b <;> simp [S200X_P, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hY]

theorem S200X_P_mul (a b : F) : S200X_P m a * S200X_P m b = S200X_P m (a + b) := by
  simp [S200X_P, Matrix.fromBlocks_multiply, add_smul, add_comm]

theorem S200X_P_zero : S200X_P m (0 : F) = 1 := by
  simp [S200X_P, Matrix.fromBlocks_one]

theorem S200X_xP_mem (x : bahturinBlockLieAlgebra F m) (n : F) :
    (x : S200X_M F m) * S200X_P m n ∈ bahturinBlockLieAlgebra F m := by
  rw [S200X_memL]
  refine ⟨fun i j => ?_, ?_⟩
  · rcases j with j|j
    · rw [S200X_xP_inl, S200X_low]
    · rw [S200X_xP_inr, S200X_low, S200X_low]; simp
  · simp only [S200X_xP_inl]; exact S200X_tr x

def S200X_sh (n : F) : bahturinBlockLieAlgebra F m →ₗ[F] bahturinBlockLieAlgebra F m where
  toFun x := ⟨(x : S200X_M F m) * S200X_P m n, S200X_xP_mem x n⟩
  map_add' x y := by apply Subtype.ext; simp [add_mul]
  map_smul' c x := by apply Subtype.ext; simp

theorem S200X_sh_val (n : F) (x : bahturinBlockLieAlgebra F m) :
    ((S200X_sh n x : bahturinBlockLieAlgebra F m) : S200X_M F m) =
      (x : S200X_M F m) * S200X_P m n := rfl

theorem S200X_sh_lie (n : F) (x y : bahturinBlockLieAlgebra F m) :
    S200X_sh n ⁅x, y⁆ = ⁅S200X_sh n x, S200X_sh n y⁆ := by
  apply Subtype.ext
  rw [S200X_lieval, S200X_sh_val, S200X_sh_val, S200X_sh_val, S200X_lieval]
  have h1 : (x : S200X_M F m) * S200X_P m n * ((y : S200X_M F m) * S200X_P m n) =
      (x : S200X_M F m) * y * S200X_P m n := by
    rw [← mul_assoc, mul_assoc (x : S200X_M F m), S200X_Pmul _ (S200X_low y)]
  have h2 : (y : S200X_M F m) * S200X_P m n * ((x : S200X_M F m) * S200X_P m n) =
      (y : S200X_M F m) * x * S200X_P m n := by
    rw [← mul_assoc, mul_assoc (y : S200X_M F m), S200X_Pmul _ (S200X_low x)]
  rw [h1, h2, sub_mul]

theorem S200X_sh_comp (a b : F) (x : bahturinBlockLieAlgebra F m) :
    S200X_sh a (S200X_sh b x) = S200X_sh (b + a) x := by
  apply Subtype.ext
  simp only [S200X_sh_val, mul_assoc, S200X_P_mul]

theorem S200X_sh_zero (x : bahturinBlockLieAlgebra F m) : S200X_sh (0 : F) x = x := by
  apply Subtype.ext
  simp only [S200X_sh_val, S200X_P_zero, mul_one]

def S200X_phi : bahturinBlockLieAlgebra F m ≃ₗ⁅F⁆ bahturinBlockLieAlgebra F m :=
  { toFun := S200X_sh (1 : F)
    map_add' := map_add _
    map_smul' := map_smul _
    map_lie' := fun {x y} => S200X_sh_lie 1 x y
    invFun := S200X_sh (-1 : F)
    left_inv := fun x => by
      show S200X_sh (-1 : F) (S200X_sh 1 x) = x
      rw [S200X_sh_comp]; norm_num [S200X_sh_zero]
    right_inv := fun x => by
      show S200X_sh (1 : F) (S200X_sh (-1) x) = x
      rw [S200X_sh_comp]; norm_num [S200X_sh_zero] }

theorem S200X_phi_shift (a : bahturinBlockLieAlgebra F m) :
    ((S200X_phi a : bahturinBlockLieAlgebra F m) : S200X_M F m) = blockShift m a := by
  change (a : S200X_M F m) * S200X_P m 1 = _
  ext (i|i) (j|j)
  · rw [S200X_xP_inl]; rfl
  · rw [S200X_xP_inr, one_mul, add_comm]; rfl
  · rw [S200X_xP_inl, S200X_low]; rfl
  · rw [S200X_xP_inr, S200X_low, S200X_low, mul_zero, add_zero]; rfl

theorem S200X_phi_pow (n : ℤ) (a : bahturinBlockLieAlgebra F m) :
    (((S200X_phi (F := F) (m := m)).toLinearEquiv.toEquiv : Equiv.Perm _) ^ n) a =
      S200X_sh (n : F) a := by
  induction n using Int.induction_on generalizing a with
  | zero => simp [S200X_sh_zero]
  | succ n ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    rw [show (S200X_phi (F := F) (m := m)).toLinearEquiv.toEquiv a = S200X_sh 1 a from rfl,
      S200X_sh_comp]
    push_cast; rw [add_comm]
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    rw [show (S200X_phi (F := F) (m := m)).toLinearEquiv.toEquiv⁻¹ a = S200X_sh (-1) a from rfl,
      S200X_sh_comp]
    push_cast; ring_nf

def S200X_G : Multiplicative ℤ →* Module.End F (bahturinBlockLieAlgebra F m) where
  toFun g := S200X_sh (((Multiplicative.toAdd g : ℤ)) : F)
  map_one' := by ext1 x; simp [S200X_sh_zero]
  map_mul' g h := by
    ext1 x
    simp only [Module.End.mul_apply, S200X_sh_comp, toAdd_mul, Int.cast_add, add_comm]

def S200X_alpha : MonoidAlgebra F (Multiplicative ℤ) →ₐ[F]
    Module.End F (bahturinBlockLieAlgebra F m) :=
  MonoidAlgebra.lift F (Module.End F (bahturinBlockLieAlgebra F m)) (Multiplicative ℤ) S200X_G

theorem S200X_alpha_single (g : Multiplicative ℤ) (r : F) (a : bahturinBlockLieAlgebra F m) :
    S200X_alpha (MonoidAlgebra.single g r) a = r • S200X_sh (((Multiplicative.toAdd g : ℤ)) : F) a := by
  simp [S200X_alpha, MonoidAlgebra.lift_single, S200X_G]

theorem S200X_tensorSum {A B X : Type*} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    [AddCommGroup X] [Module F X] (z : A ⊗[F] B) (Bl : A →ₗ[F] B →ₗ[F] X) :
    tensorSum z (fun a b => Bl a b) = TensorProduct.lift Bl z := by
  unfold tensorSum
  conv_rhs => rw [(TensorProduct.exists_finset z).choose_spec]
  rw [map_sum]
  simp [TensorProduct.lift.tmul]

def S200X_bil (a b : bahturinBlockLieAlgebra F m) :
    MonoidAlgebra F (Multiplicative ℤ) →ₗ[F] MonoidAlgebra F (Multiplicative ℤ) →ₗ[F]
      bahturinBlockLieAlgebra F m :=
  LinearMap.mk₂ F (fun h1 h2 => ⁅S200X_alpha h1 a, S200X_alpha h2 b⁆)
    (by intros; simp [add_lie]) (by intros; simp [smul_lie])
    (by intros; simp [lie_add]) (by intros; simp [lie_smul])

theorem S200X_moduleLie : ModuleLie (S200X_alpha (F := F) (m := m)) := by
  intro h a b
  have := S200X_tensorSum (F := F) (Coalgebra.comul (R := F) h) (S200X_bil a b)
  simp only [S200X_bil, LinearMap.mk₂_apply] at this
  rw [this]
  clear this
  induction h using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, LinearMap.add_apply, hx, hy]
  | single g r =>
    rw [MonoidAlgebra.comul_single]
    simp [S200X_bil, S200X_alpha_single, S200X_sh_lie, smul_lie, lie_smul]

theorem S200X_sh_R (n : F) (v : bahturinBlockLieAlgebra F m) (hv : v ∈ blockRadical F m) :
    S200X_sh n v ∈ blockRadical F m := by
  rw [S200X_memR] at hv ⊢
  intro i j
  rw [S200X_sh_val, S200X_xP_inl, hv]

theorem S200X_stable : ActionStable (S200X_alpha (F := F) (m := m)) (blockRadical F m) := by
  intro h v hv
  induction h using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simpa using add_mem hx hy
  | single g r =>
    rw [S200X_alpha_single]
    exact Submodule.smul_mem _ _ (S200X_sh_R _ v hv)

theorem S200X_noB (hm : 2 ≤ m) : ¬ ∃ B : LieSubalgebra F (bahturinBlockLieAlgebra F m),
    Semisimple F B ∧ ActionStable (S200X_alpha (F := F) (m := m)) B.toSubmodule ∧
      IsCompl B.toSubmodule (blockRadical F m) := by
  rintro ⟨B, -, hst, hc⟩
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
  set e := S200X_E (F := F) ⟨0, by omega⟩ ⟨1, by omega⟩ h01
  have he : e ∈ B.toSubmodule ⊔ blockRadical F m := by rw [hc.sup_eq_top]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 he
  have h1 : S200X_alpha (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1) y ∈ B.toSubmodule :=
    hst _ y hy
  rw [S200X_alpha_single, one_smul] at h1
  have hw : S200X_sh (((Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) : ℤ)) : F) y - y ∈
      B.toSubmodule ⊓ blockRadical F m := by
    refine ⟨sub_mem h1 hy, ?_⟩
    show _ ∈ blockRadical F m
    rw [S200X_memR]
    intro i j
    rw [AddSubgroupClass.coe_sub, Matrix.sub_apply, S200X_sh_val, S200X_xP_inl, sub_self]
  rw [hc.inf_eq_bot, Submodule.mem_bot] at hw
  have hw2 := congrArg (fun w : bahturinBlockLieAlgebra F m =>
    (w : S200X_M F m) (Sum.inl ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩)) hw
  simp only [AddSubgroupClass.coe_sub, Matrix.sub_apply, S200X_sh_val, S200X_xP_inr,
    toAdd_ofAdd, Int.cast_one, one_mul, add_sub_cancel_left, ZeroMemClass.coe_zero,
    Matrix.zero_apply] at hw2
  have hz2 := (S200X_memR z).1 hz ⟨0, by omega⟩ ⟨1, by omega⟩
  have he2 := congrArg (fun w : bahturinBlockLieAlgebra F m =>
    (w : S200X_M F m) (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨1, by omega⟩)) hyz
  simp only [AddMemClass.coe_add, Matrix.add_apply, hw2, hz2, add_zero] at he2
  rw [S200X_E_val, Matrix.single_apply_same] at he2
  exact zero_ne_one he2

theorem S200X_main [CharZero F] (m : ℕ) (hm : 2 ≤ m) :
    (∀ X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F,
      X ∈ bahturinBlockLieAlgebra F m ↔ ∃ C D : Matrix (Fin m) (Fin m) F,
        Matrix.trace C = 0 ∧ X = blockElement m C D) ∧
    (LieAlgebra.radical F (bahturinBlockLieAlgebra F m)).toSubmodule = blockRadical F m ∧
    (lieNilpotentRadical F (bahturinBlockLieAlgebra F m)).toSubmodule = blockRadical F m ∧
    ∃ phi : bahturinBlockLieAlgebra F m ≃ₗ⁅F⁆ bahturinBlockLieAlgebra F m,
      (∀ a, (phi a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) = blockShift m a) ∧
      Function.Injective (fun n : ℤ =>
        (phi.toLinearEquiv.toEquiv : Equiv.Perm (bahturinBlockLieAlgebra F m)) ^ n) ∧
      ∃ alpha : MonoidAlgebra F (Multiplicative ℤ) →ₐ[F] Module.End F (bahturinBlockLieAlgebra F m),
        (∀ n : ℤ, ∀ a, alpha (MonoidAlgebra.single (Multiplicative.ofAdd n) 1) a =
          ((phi.toLinearEquiv.toEquiv : Equiv.Perm (bahturinBlockLieAlgebra F m)) ^ n) a) ∧
        ModuleLie alpha ∧ ActionStable alpha (blockRadical F m) ∧
        ¬ ∃ B : LieSubalgebra F (bahturinBlockLieAlgebra F m), Semisimple F B ∧
          ActionStable alpha B.toSubmodule ∧ IsCompl B.toSubmodule (blockRadical F m) := by
  refine ⟨fun X => by rw [S200X_memL, S200X_good_iff], by rw [S200X_rad.1]; rfl,
    by rw [S200X_rad.2]; rfl, S200X_phi, S200X_phi_shift, ?_, S200X_alpha, ?_, S200X_moduleLie,
    S200X_stable, S200X_noB hm⟩
  · intro n k hnk
    have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
    have := congrArg (fun f : Equiv.Perm (bahturinBlockLieAlgebra F m) =>
      ((f (S200X_E (F := F) ⟨0, by omega⟩ ⟨1, by omega⟩ h01) : bahturinBlockLieAlgebra F m) :
        S200X_M F m) (Sum.inl ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩)) hnk
    simp only [S200X_phi_pow, S200X_sh_val, S200X_xP_inr, S200X_E_val,
      Matrix.single_apply_same] at this
    simp only [Matrix.single_apply_of_ne _ _ _ _ _ (by simp : ¬ ((Sum.inl ⟨0, by omega⟩ :
      Fin m ⊕ Fin m) = Sum.inl ⟨0, by omega⟩ ∧ (Sum.inl ⟨1, by omega⟩ : Fin m ⊕ Fin m) =
        Sum.inr ⟨1, by omega⟩)), zero_add, mul_one] at this
    exact_mod_cast this
  · intro n a
    rw [S200X_alpha_single, one_smul, S200X_phi_pow, toAdd_ofAdd]

end S200X

end

end QAlgorithms.Papers.Independent.Next46.P22

section

open QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

attribute [local instance] LieRing.ofAssociativeRing

theorem solution [CharZero F] (m : ℕ) (hm : 2 ≤ m) :
    (∀ X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F,
      X ∈ bahturinBlockLieAlgebra F m ↔ ∃ C D : Matrix (Fin m) (Fin m) F,
        Matrix.trace C = 0 ∧ X = blockElement m C D) ∧
    (LieAlgebra.radical F (bahturinBlockLieAlgebra F m)).toSubmodule = blockRadical F m ∧
    (lieNilpotentRadical F (bahturinBlockLieAlgebra F m)).toSubmodule = blockRadical F m ∧
    ∃ phi : bahturinBlockLieAlgebra F m ≃ₗ⁅F⁆ bahturinBlockLieAlgebra F m,
      (∀ a, (phi a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) = blockShift m a) ∧
      Function.Injective (fun n : ℤ =>
        (phi.toLinearEquiv.toEquiv : Equiv.Perm (bahturinBlockLieAlgebra F m)) ^ n) ∧
      ∃ alpha : MonoidAlgebra F (Multiplicative ℤ) →ₐ[F] Module.End F (bahturinBlockLieAlgebra F m),
        (∀ n : ℤ, ∀ a, alpha (MonoidAlgebra.single (Multiplicative.ofAdd n) 1) a =
          ((phi.toLinearEquiv.toEquiv : Equiv.Perm (bahturinBlockLieAlgebra F m)) ^ n) a) ∧
        ModuleLie alpha ∧ ActionStable alpha (blockRadical F m) ∧
        ¬ ∃ B : LieSubalgebra F (bahturinBlockLieAlgebra F m), Semisimple F B ∧
          ActionStable alpha B.toSubmodule ∧ IsCompl B.toSubmodule (blockRadical F m) :=
  S200X_main m hm

end

end

