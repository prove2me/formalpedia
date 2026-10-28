-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.tensor_homology_kunneth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T03:24:54.138925+00:00
-- url     : https://prove2.me/submissions/1d9f3410-739e-4b08-9769-dbf5918eb1ed

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix Kronecker

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace KunnethAux

open QAlgorithms.Surgery

/-- Graded matrix: nonzero entries shift degree by `k`. -/
def IsDeg {X Y : Type} (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (M : Matrix X Y (ZMod 2)) : Prop :=
  ∀ a b, M a b ≠ 0 → dX a = dY b + k

lemma IsDeg.mul {X Y Z : Type} [Fintype Y] {dX : X → ℤ} {dY : Y → ℤ} {dZ : Z → ℤ} {m n : ℤ}
    {A : Matrix X Y (ZMod 2)} {B : Matrix Y Z (ZMod 2)}
    (hA : IsDeg dX dY m A) (hB : IsDeg dY dZ n B) : IsDeg dX dZ (m + n) (A * B) := by
  intro a c h
  rw [Matrix.mul_apply] at h
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := hA a b (left_ne_zero_of_mul hb)
  have h2 := hB b c (right_ne_zero_of_mul hb)
  omega

lemma IsDeg.add {X Y : Type} {dX : X → ℤ} {dY : Y → ℤ} {k : ℤ}
    {A B : Matrix X Y (ZMod 2)} (hA : IsDeg dX dY k A) (hB : IsDeg dX dY k B) :
    IsDeg dX dY k (A + B) := by
  intro a b h
  by_cases ha : A a b = 0
  · rw [Matrix.add_apply, ha, zero_add] at h; exact hB a b h
  · exact hA a b ha

lemma IsDeg.sub {X Y : Type} {dX : X → ℤ} {dY : Y → ℤ} {k : ℤ}
    {A B : Matrix X Y (ZMod 2)} (hA : IsDeg dX dY k A) (hB : IsDeg dX dY k B) :
    IsDeg dX dY k (A - B) := by
  intro a b h
  by_cases ha : A a b = 0
  · rw [Matrix.sub_apply, ha, zero_sub, neg_ne_zero] at h; exact hB a b h
  · exact hA a b ha

lemma IsDeg.of_eq {X Y : Type} {dX : X → ℤ} {dY : Y → ℤ} {k k' : ℤ}
    {A : Matrix X Y (ZMod 2)} (hA : IsDeg dX dY k A) (h : k = k') : IsDeg dX dY k' A := h ▸ hA

lemma isDeg_one {X : Type} [DecidableEq X] (dX : X → ℤ) : IsDeg dX dX 0 (1 : Matrix X X (ZMod 2)) := by
  intro a b h
  by_cases hab : a = b
  · subst hab; simp
  · exact absurd (Matrix.one_apply_ne hab) h

lemma isDeg_diff (C : BasedBinaryComplex) : IsDeg C.degree C.degree (-1) C.differential := by
  intro a b h; have := C.lowers a b h; omega

lemma mat_add_self {X Y : Type} (M : Matrix X Y (ZMod 2)) : M + M = 0 := by
  ext a b; exact CharTwo.add_self_eq_zero (M a b)

lemma mat_sub_eq_add {X Y : Type} (M N : Matrix X Y (ZMod 2)) : M - N = M + N := by
  rw [sub_eq_add_neg]; congr 1
  ext a b; simp only [Matrix.neg_apply]; exact ZMod.neg_eq_self_mod_two (N a b)

/-- Every square matrix over a field has a generalized inverse. -/
lemma exists_ginv {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n (ZMod 2)) :
    ∃ G : Matrix n n (ZMod 2), A * G * A = A := by
  let f := Matrix.toLin' A
  obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨p, hp⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  refine ⟨LinearMap.toMatrix' (r ∘ₗ p), ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply]
  have h1 : p (f v) = f.rangeRestrict v := by
    have := LinearMap.congr_fun hp (f.rangeRestrict v)
    simpa using this
  have h2 := LinearMap.congr_fun hr (f.rangeRestrict v)
  change f (r (p (f v))) = f v
  rw [h1]
  have e : f (r (f.rangeRestrict v)) =
      ((f.rangeRestrict (r (f.rangeRestrict v)) : LinearMap.range f) : n → ZMod 2) := rfl
  rw [e]
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
  rw [h2]; rfl

/-- Degree-`k` part of a matrix. -/
def degPart {X Y : Type} (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (M : Matrix X Y (ZMod 2)) :
    Matrix X Y (ZMod 2) :=
  Matrix.of fun a b => if dX a = dY b + k then M a b else 0

lemma degPart_isDeg {X Y : Type} (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (M : Matrix X Y (ZMod 2)) :
    IsDeg dX dY k (degPart dX dY k M) := by
  intro a b h
  simp only [degPart, Matrix.of_apply] at h
  by_contra hc; rw [if_neg hc] at h; exact h rfl

lemma exists_graded_ginv (C : BasedBinaryComplex) :
    ∃ s, IsDeg C.degree C.degree 1 s ∧ C.differential * s * C.differential = C.differential := by
  obtain ⟨g, hg⟩ := exists_ginv C.differential
  refine ⟨degPart C.degree C.degree 1 g, degPart_isDeg _ _ _ _, ?_⟩
  ext a c
  by_cases hd : C.degree a + 1 = C.degree c
  · conv_rhs => rw [← hg]
    simp only [Matrix.mul_apply, degPart, Matrix.of_apply]
    apply Finset.sum_congr rfl; intro b' _
    by_cases h2 : C.differential b' c = 0
    · simp [h2]
    congr 1; apply Finset.sum_congr rfl; intro b _
    by_cases h1 : C.differential a b = 0
    · simp [h1]
    have := C.lowers a b h1; have := C.lowers b' c h2
    rw [if_pos (by omega)]
  · have hz : C.differential a c = 0 := by
      by_contra h; exact hd (C.lowers a c h)
    rw [hz]
    simp only [Matrix.mul_apply, degPart, Matrix.of_apply]
    apply Finset.sum_eq_zero; intro b' _
    by_cases h2 : C.differential b' c = 0
    · simp [h2]
    rw [Finset.sum_eq_zero, zero_mul]; intro b _
    by_cases h1 : C.differential a b = 0
    · simp [h1]
    have := C.lowers a b h1; have := C.lowers b' c h2
    rw [if_neg (by omega), mul_zero]

lemma exists_splitting (C : BasedBinaryComplex) :
    ∃ s, IsDeg C.degree C.degree 1 s ∧ s * s = 0 ∧
      C.differential * s * C.differential = C.differential := by
  obtain ⟨s0, hs0, h0⟩ := exists_graded_ginv C
  have hd := isDeg_diff C
  have hs1 : IsDeg C.degree C.degree 1 (s0 * C.differential * s0) :=
    ((hs0.mul hd).mul hs0).of_eq (by ring)
  have h1 : C.differential * (s0 * C.differential * s0) * C.differential = C.differential := by
    have : C.differential * (s0 * C.differential * s0) * C.differential =
        (C.differential * s0 * C.differential) * s0 * C.differential := by
      simp only [Matrix.mul_assoc]
    rw [this, h0, h0]
  have r1 : (s0 * C.differential * s0) * C.differential * (s0 * C.differential * s0) =
      s0 * C.differential * s0 := by
    have : (s0 * C.differential * s0) * C.differential * (s0 * C.differential * s0) =
        s0 * ((C.differential * s0 * C.differential) * s0 * C.differential) * s0 := by
      simp only [Matrix.mul_assoc]
    rw [this, h0, h0]
  set s1 := s0 * C.differential * s0 with hs1def
  refine ⟨s1 - s1 * s1 * C.differential, ?_, ?_, ?_⟩
  · exact hs1.sub (((hs1.mul hs1).mul hd).of_eq (by ring))
  · have e : (1 - s1 * C.differential) * s1 = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, r1, sub_self]
    have : s1 - s1 * s1 * C.differential = s1 * (1 - s1 * C.differential) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    rw [this, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - s1 * C.differential), e,
      Matrix.zero_mul, Matrix.mul_zero]
  · rw [Matrix.mul_sub, Matrix.sub_mul, h1]
    have : C.differential * (s1 * s1 * C.differential) * C.differential = 0 := by
      simp only [Matrix.mul_assoc, C.square, Matrix.mul_zero]
    rw [this, sub_zero]

/-- The harmonic projector `h = 1 + d s + s d`. -/
lemma harmonic_props (C : BasedBinaryComplex) (s : Matrix C.Cell C.Cell (ZMod 2))
    (hs : IsDeg C.degree C.degree 1 s) (hss : s * s = 0)
    (hdsd : C.differential * s * C.differential = C.differential) :
    let h := 1 + C.differential * s + s * C.differential
    IsDeg C.degree C.degree 0 h ∧ C.differential * h = 0 ∧ h * C.differential = 0 ∧ h * h = h := by
  intro h
  have hd := isDeg_diff C
  have hdd := C.square
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((isDeg_one _).add ((hd.mul hs).of_eq (by ring))).add ((hs.mul hd).of_eq (by ring))
  · simp only [h, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hdd, Matrix.zero_mul,
      add_zero, hdsd, mat_add_self]
  · simp only [h, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hdd, Matrix.mul_zero,
      add_zero]
    rw [← Matrix.mul_assoc, hdsd, mat_add_self]
  · have hHd : h * C.differential = 0 := by
      simp only [h, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hdd, Matrix.mul_zero,
        add_zero]
      rw [← Matrix.mul_assoc, hdsd, mat_add_self]
    have hHsd : h * s * C.differential = 0 := by
      simp only [h, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hss, Matrix.mul_zero,
        add_zero]
      rw [← Matrix.mul_assoc C.differential s C.differential, hdsd, mat_add_self]
    calc h * h = h * (1 + C.differential * s + s * C.differential) := rfl
      _ = h + (h * C.differential) * s + (h * s) * C.differential := by
        simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
      _ = h := by rw [hHd, hHsd, Matrix.zero_mul, add_zero, add_zero]

/-- Block of a global matrix between two degree pieces. -/
abbrev blk (C : BasedBinaryComplex) (i j : ℤ) (M : Matrix C.Cell C.Cell (ZMod 2)) :
    Matrix (Basis C i) (Basis C j) (ZMod 2) := M.submatrix Subtype.val Subtype.val

lemma blk_mul (C : BasedBinaryComplex) (i m j : ℤ) (A B : Matrix C.Cell C.Cell (ZMod 2))
    (hB : ∀ x c, B x c ≠ 0 → C.degree c = j → C.degree x = m) :
    blk C i j (A * B) = blk C i m A * blk C m j B := by
  ext a c
  simp only [blk, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x => C.degree x = m)]
  have : ∑ x : {x // ¬ C.degree x = m}, A a.1 x.1 * B x.1 c.1 = 0 :=
    Finset.sum_eq_zero fun x _ => by
      by_cases hb : B x.1 c.1 = 0
      · simp [hb]
      · exact absurd (hB _ _ hb c.2) x.2
  rw [this, add_zero]

lemma blk_add (C : BasedBinaryComplex) (i j : ℤ) (A B : Matrix C.Cell C.Cell (ZMod 2)) :
    blk C i j (A + B) = blk C i j A + blk C i j B := rfl

lemma blk_zero (C : BasedBinaryComplex) (i j : ℤ) :
    blk C i j (0 : Matrix C.Cell C.Cell (ZMod 2)) = 0 := rfl

lemma blk_one (C : BasedBinaryComplex) (i : ℤ) :
    blk C i i (1 : Matrix C.Cell C.Cell (ZMod 2)) = 1 := by
  ext a b
  simp only [blk, Matrix.submatrix_apply, Matrix.one_apply, Subtype.ext_iff]

/-- Homology dimension equals the rank of a harmonic projector block. -/
lemma finrank_homology_eq (C : BasedBinaryComplex) (H S : Matrix C.Cell C.Cell (ZMod 2))
    (hH : IsDeg C.degree C.degree 0 H) (hS : IsDeg C.degree C.degree 1 S)
    (hHS : H = 1 + C.differential * S + S * C.differential)
    (hdH : C.differential * H = 0) (hHd : H * C.differential = 0) (hHH : H * H = H) (i : ℤ) :
    Module.finrank (ZMod 2) (Homology C i) = (blk C i i H).rank := by
  have hd := isDeg_diff C
  have e1 : blk C i i H = 1 + blk C i (i+1) C.differential * blk C (i+1) i S +
      blk C i (i-1) S * blk C (i-1) i C.differential := by
    conv_lhs => rw [hHS]
    rw [blk_add, blk_add, blk_one,
      blk_mul C i (i+1) i _ _ (fun x c h hc => by have := hS x c h; omega),
      blk_mul C i (i-1) i _ _ (fun x c h hc => by have := hd x c h; omega)]
  have fDH : blk C (i-1) i C.differential * blk C i i H = 0 := by
    rw [← blk_mul C (i-1) i i _ _ (fun x c h hc => by have := hH x c h; omega), hdH, blk_zero]
  have fHU : blk C i i H * blk C i (i+1) C.differential = 0 := by
    rw [← blk_mul C i i (i+1) _ _ (fun x c h hc => by have := hd x c h; omega), hHd, blk_zero]
  have fDU : blk C (i-1) i C.differential * blk C i (i+1) C.differential = 0 := by
    rw [← blk_mul C (i-1) i (i+1) _ _ (fun x c h hc => by have := hd x c h; omega), C.square,
      blk_zero]
  have fHH : blk C i i H * blk C i i H = blk C i i H := by
    rw [← blk_mul C i i i _ _ (fun x c h hc => by have := hH x c h; omega), hHH]
  set Hi := blk C i i H with hHi
  set D := blk C (i-1) i C.differential with hD
  set U := blk C i (i+1) C.differential with hU
  have hcyc : cycles C i = LinearMap.ker D.mulVecLin := rfl
  have hbd : boundaries C i = (LinearMap.range U.mulVecLin).comap (cycles C i).subtype := rfl
  have hle1 : LinearMap.range Hi.mulVecLin ≤ cycles C i := by
    rintro _ ⟨u, rfl⟩
    rw [hcyc, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, fDH, Matrix.zero_mulVec]
  have hle2 : LinearMap.range U.mulVecLin ≤ cycles C i := by
    rintro _ ⟨u, rfl⟩
    rw [hcyc, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, fDU, Matrix.zero_mulVec]
  have hsup : LinearMap.range Hi.mulVecLin ⊔ LinearMap.range U.mulVecLin = cycles C i := by
    refine le_antisymm (sup_le hle1 hle2) ?_
    intro z hz
    rw [hcyc, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
    have hz' : Hi *ᵥ z = z + U *ᵥ (blk C (i+1) i S *ᵥ z) := by
      rw [e1, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, add_zero]
    have : z = Hi *ᵥ z - U *ᵥ (blk C (i+1) i S *ᵥ z) := by rw [hz']; abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨z, rfl⟩)
      (Submodule.mem_sup_right ⟨_, rfl⟩)
  have hdisj : LinearMap.range Hi.mulVecLin ⊓ LinearMap.range U.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    rw [Submodule.mem_bot]
    simp only [Matrix.mulVecLin_apply] at hv ⊢
    calc Hi *ᵥ u = Hi *ᵥ (Hi *ᵥ u) := by rw [Matrix.mulVec_mulVec, fHH]
      _ = Hi *ᵥ (U *ᵥ v) := by rw [hv]
      _ = 0 := by rw [Matrix.mulVec_mulVec, fHU, Matrix.zero_mulVec]
  have fin1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Hi.mulVecLin)
    (LinearMap.range U.mulVecLin)
  rw [hsup, hdisj, finrank_bot, add_zero] at fin1
  have fin2 := Submodule.finrank_quotient_add_finrank (boundaries C i)
  have fin3 : Module.finrank (ZMod 2) (boundaries C i) =
      Module.finrank (ZMod 2) (LinearMap.range U.mulVecLin) := by
    rw [hbd]; exact (Submodule.comapSubtypeEquivOfLe hle2).finrank_eq
  have hrk : Hi.rank = Module.finrank (ZMod 2) (LinearMap.range Hi.mulVecLin) := rfl
  rw [hrk]
  show Module.finrank (ZMod 2) (↥(cycles C i) ⧸ boundaries C i) = _
  omega

lemma isDeg_kron (C D : BasedBinaryComplex) {m n : ℤ} {A : Matrix C.Cell C.Cell (ZMod 2)}
    {B : Matrix D.Cell D.Cell (ZMod 2)} (hA : IsDeg C.degree C.degree m A)
    (hB : IsDeg D.degree D.degree n B) :
    IsDeg (fun p : C.Cell × D.Cell => C.degree p.1 + D.degree p.2)
      (fun p : C.Cell × D.Cell => C.degree p.1 + D.degree p.2) (m + n)
      ((A ⊗ₖ B)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Matrix.kroneckerMap_apply] at h
  have h1 := hA a a' (left_ne_zero_of_mul h)
  have h2 := hB b b' (right_ne_zero_of_mul h)
  show C.degree a + D.degree b = C.degree a' + D.degree b' + (m + n)
  omega

lemma kron_one_one' (C D : BasedBinaryComplex) :
    ((1 : Matrix C.Cell C.Cell (ZMod 2)) ⊗ₖ (1 : Matrix D.Cell D.Cell (ZMod 2))) =
      (1 : Matrix (C.Cell × D.Cell) (C.Cell × D.Cell) (ZMod 2)) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]

lemma tensor_props (C D : BasedBinaryComplex) (s h : Matrix C.Cell C.Cell (ZMod 2))
    (s' h' : Matrix D.Cell D.Cell (ZMod 2))
    (hs : IsDeg C.degree C.degree 1 s) (hs' : IsDeg D.degree D.degree 1 s')
    (hH : IsDeg C.degree C.degree 0 h) (hH' : IsDeg D.degree D.degree 0 h')
    (hh : h = 1 + C.differential * s + s * C.differential)
    (hh' : h' = 1 + D.differential * s' + s' * D.differential)
    (dh : C.differential * h = 0) (hd : h * C.differential = 0) (hhh : h * h = h)
    (dh' : D.differential * h' = 0) (hd' : h' * D.differential = 0) (hhh' : h' * h' = h') :
    IsDeg (fun p : C.Cell × D.Cell => C.degree p.1 + D.degree p.2)
      (fun p : C.Cell × D.Cell => C.degree p.1 + D.degree p.2) 0 ((h ⊗ₖ h')) ∧
    IsDeg (fun p : C.Cell × D.Cell => C.degree p.1 + D.degree p.2)
      (fun p : C.Cell × D.Cell => C.degree p.1 + D.degree p.2) 1
      ((s ⊗ₖ 1) + (h ⊗ₖ s')) ∧
    (h ⊗ₖ h') = 1 + ((C.differential ⊗ₖ 1) + (1 ⊗ₖ D.differential)) *
      ((s ⊗ₖ 1) + (h ⊗ₖ s')) +
      ((s ⊗ₖ 1) + (h ⊗ₖ s')) * ((C.differential ⊗ₖ 1) + (1 ⊗ₖ D.differential)) ∧
    ((C.differential ⊗ₖ 1) + (1 ⊗ₖ D.differential)) * (h ⊗ₖ h') = 0 ∧
    (h ⊗ₖ h') * ((C.differential ⊗ₖ 1) + (1 ⊗ₖ D.differential)) = 0 ∧
    (h ⊗ₖ h') * (h ⊗ₖ h') = (h ⊗ₖ h') := by
  refine ⟨(isDeg_kron C D hH hH').of_eq (by ring),
    ((isDeg_kron C D hs (isDeg_one _)).of_eq (by ring)).add
      ((isDeg_kron C D hH hs').of_eq (by ring)), ?_, ?_, ?_, ?_⟩
  · have e1 : ((C.differential ⊗ₖ 1) + (1 ⊗ₖ D.differential)) * ((s ⊗ₖ 1) + (h ⊗ₖ s')) =
        ((C.differential * s) ⊗ₖ 1) + (s ⊗ₖ D.differential) +
          (h ⊗ₖ (D.differential * s')) := by
      simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
        Matrix.one_mul, dh, Matrix.zero_kronecker, add_zero, zero_add] <;> abel
    have e2 : ((s ⊗ₖ 1) + (h ⊗ₖ s')) * ((C.differential ⊗ₖ 1) + (1 ⊗ₖ D.differential)) =
        ((s * C.differential) ⊗ₖ 1) + (s ⊗ₖ D.differential) +
          (h ⊗ₖ (s' * D.differential)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
        Matrix.one_mul, hd, Matrix.zero_kronecker, add_zero, zero_add] <;> abel
    have c1 : C.differential * s + s * C.differential = h + 1 := by
      rw [hh]
      calc C.differential * s + s * C.differential
          = C.differential * s + s * C.differential + (1 + 1) := by rw [mat_add_self, add_zero]
        _ = 1 + C.differential * s + s * C.differential + 1 := by abel
    have c2 : D.differential * s' + s' * D.differential = h' + 1 := by
      rw [hh']
      calc D.differential * s' + s' * D.differential
          = D.differential * s' + s' * D.differential + (1 + 1) := by rw [mat_add_self, add_zero]
        _ = 1 + D.differential * s' + s' * D.differential + 1 := by abel
    have k1 : ((C.differential * s) ⊗ₖ (1 : Matrix D.Cell D.Cell (ZMod 2))) +
        ((s * C.differential) ⊗ₖ 1) = (h ⊗ₖ 1) + 1 := by
      rw [← Matrix.add_kronecker, c1, Matrix.add_kronecker, kron_one_one']
    have k2 : (h ⊗ₖ (D.differential * s')) + (h ⊗ₖ (s' * D.differential)) =
        (h ⊗ₖ h') + (h ⊗ₖ 1) := by
      rw [← Matrix.kronecker_add, c2, Matrix.kronecker_add]
    rw [e1, e2]
    calc (h ⊗ₖ h')
        = (h ⊗ₖ h') + (1 + 1) + ((h ⊗ₖ 1) + (h ⊗ₖ 1)) +
          ((s ⊗ₖ D.differential) + (s ⊗ₖ D.differential)) := by
          rw [mat_add_self (1 : Matrix (C.Cell × D.Cell) (C.Cell × D.Cell) (ZMod 2)),
            mat_add_self ((h ⊗ₖ (1 : Matrix D.Cell D.Cell (ZMod 2)))),
            mat_add_self ((s ⊗ₖ D.differential))]
          simp only [add_zero]
      _ = 1 + ((h ⊗ₖ 1) + 1) + ((h ⊗ₖ h') + (h ⊗ₖ 1)) +
          ((s ⊗ₖ D.differential) + (s ⊗ₖ D.differential)) := by abel
      _ = _ := by rw [← k1, ← k2]; abel
  · rw [Matrix.add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, dh, dh',
      Matrix.zero_kronecker, Matrix.kronecker_zero, add_zero]
  · rw [Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hd, hd',
      Matrix.zero_kronecker, Matrix.kronecker_zero, add_zero]
  · rw [← Matrix.mul_kronecker_mul, hhh, hhh']

lemma finrank_range_tmap {V W V' W' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup V'] [Module (ZMod 2) V']
    [AddCommGroup W'] [Module (ZMod 2) W'] [FiniteDimensional (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W']
    (f : V →ₗ[ZMod 2] W) (g : V' →ₗ[ZMod 2] W') :
    Module.finrank (ZMod 2) (LinearMap.range (TensorProduct.map f g)) =
      Module.finrank (ZMod 2) (LinearMap.range f) * Module.finrank (ZMod 2) (LinearMap.range g) := by
  have hc : TensorProduct.map f g = TensorProduct.map (LinearMap.range f).subtype
      (LinearMap.range g).subtype ∘ₗ TensorProduct.map f.rangeRestrict g.rangeRestrict := by
    rw [← TensorProduct.map_comp]; rfl
  rw [hc, LinearMap.range_comp_of_range_eq_top]
  · rw [LinearMap.finrank_range_of_inj (TensorProduct.map_injective_of_flat_flat _ _
      (Submodule.injective_subtype _) (Submodule.injective_subtype _)),
      Module.finrank_tensorProduct]
  · exact LinearMap.range_eq_top.mpr
      (TensorProduct.map_surjective f.surjective_rangeRestrict g.surjective_rangeRestrict)

lemma rank_kron {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m (ZMod 2)) (B : Matrix n n (ZMod 2)) :
    ((A ⊗ₖ B)).rank = A.rank * B.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin ((A ⊗ₖ B))
      ((Pi.basisFun (ZMod 2) m).tensorProduct (Pi.basisFun (ZMod 2) n))
      ((Pi.basisFun (ZMod 2) m).tensorProduct (Pi.basisFun (ZMod 2) n)),
    Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun (ZMod 2) m) (Pi.basisFun (ZMod 2) m),
    Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun (ZMod 2) n) (Pi.basisFun (ZMod 2) n)]
  rw [Matrix.toLin_kronecker]
  exact finrank_range_tmap _ _

end KunnethAux

namespace KunnethAux

open QAlgorithms.Surgery

lemma finrank_range_piMap {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
    [∀ i, FiniteDimensional (ZMod 2) (W i)]
    (f : ∀ i, V i →ₗ[ZMod 2] W i) :
    Module.finrank (ZMod 2) (LinearMap.range (LinearMap.piMap f)) =
      ∑ i, Module.finrank (ZMod 2) (LinearMap.range (f i)) := by
  have hc : LinearMap.piMap f = LinearMap.piMap (fun i => (LinearMap.range (f i)).subtype) ∘ₗ
      LinearMap.piMap (fun i => (f i).rangeRestrict) := by
    refine LinearMap.ext fun v => funext fun i => rfl
  rw [hc, LinearMap.range_comp_of_range_eq_top]
  · rw [LinearMap.finrank_range_of_inj, Module.finrank_pi_fintype]
    intro x y hxy; funext i; exact Subtype.ext (congr_fun hxy i)
  · rw [LinearMap.range_eq_top]; intro w
    exact ⟨fun i => ((f i).surjective_rangeRestrict (w i)).choose,
      funext fun i => ((f i).surjective_rangeRestrict (w i)).choose_spec⟩

lemma rank_blockdiag {X ι : Type} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (M : Matrix X X (ZMod 2)) (π : X → ι) (hM : ∀ x y, M x y ≠ 0 → π x = π y) :
    M.rank = ∑ j, (M.submatrix (Subtype.val : {x // π x = j} → X)
      (Subtype.val : {x // π x = j} → X)).rank := by
  let Φ : (X → ZMod 2) →ₗ[ZMod 2] (∀ j, {x // π x = j} → ZMod 2) :=
    { toFun := fun v j y => v y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro v w hvw
      funext x
      exact congr_fun (congr_fun hvw (π x)) ⟨x, rfl⟩
    · intro g
      refine ⟨fun x => g (π x) ⟨x, rfl⟩, ?_⟩
      funext j y
      rcases y with ⟨y, rfl⟩
      rfl
  let e := LinearEquiv.ofBijective Φ hΦ
  have hcomm : Φ ∘ₗ M.mulVecLin =
      LinearMap.piMap (fun j => (M.submatrix (Subtype.val : {x // π x = j} → X)
        (Subtype.val : {x // π x = j} → X)).mulVecLin) ∘ₗ Φ := by
    refine LinearMap.ext fun v => funext fun j => funext fun y => ?_
    show (M *ᵥ v) y.1 = ((M.submatrix (Subtype.val : {x // π x = j} → X)
      (Subtype.val : {x // π x = j} → X)) *ᵥ (fun z => v z.1)) y
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x => π x = j)]
    have : ∑ x : {x // ¬ π x = j}, M y.1 x.1 * v x.1 = 0 :=
      Finset.sum_eq_zero fun x _ => by
        by_cases hb : M y.1 x.1 = 0
        · simp [hb]
        · exact absurd ((hM _ _ hb).symm.trans y.2) x.2
    rw [this, add_zero]
  have h1 : M.rank = Module.finrank (ZMod 2) (LinearMap.range (Φ ∘ₗ M.mulVecLin)) := by
    rw [LinearMap.range_comp]
    exact (LinearEquiv.finrank_map_eq e _).symm
  rw [h1, hcomm, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hΦ.2),
    finrank_range_piMap]
  rfl

end KunnethAux

namespace KunnethAux

open QAlgorithms.Surgery

lemma rank_block_kron (C D : BasedBinaryComplex) (l : ℤ) (h : Matrix C.Cell C.Cell (ZMod 2))
    (h' : Matrix D.Cell D.Cell (ZMod 2)) (hH : IsDeg C.degree C.degree 0 h) :
    ((h ⊗ₖ h').submatrix
      (Subtype.val : {p : C.Cell × D.Cell // C.degree p.1 + D.degree p.2 = l} → C.Cell × D.Cell)
      (Subtype.val : {p : C.Cell × D.Cell // C.degree p.1 + D.degree p.2 = l} →
        C.Cell × D.Cell)).rank =
    ∑ j : (Finset.univ.image C.degree),
      (blk C (j : ℤ) (j : ℤ) h).rank * (blk D (l - (j : ℤ)) (l - (j : ℤ)) h').rank := by
  let π : {p : C.Cell × D.Cell // C.degree p.1 + D.degree p.2 = l} →
      (Finset.univ.image C.degree) :=
    fun x => ⟨C.degree x.1.1, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  rw [rank_blockdiag _ π ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    let e : {x // π x = j} ≃ (Basis C (j : ℤ) × Basis D (l - (j : ℤ))) :=
      { toFun := fun x => (⟨x.1.1.1, congrArg Subtype.val x.2⟩,
          ⟨x.1.1.2, by
            have h1 : C.degree x.1.1.1 = (j : ℤ) := congrArg Subtype.val x.2
            have h2 := x.1.2
            omega⟩)
        invFun := fun ab => ⟨⟨(ab.1.1, ab.2.1), by
            have h1 := ab.1.2
            have h2 := ab.2.2
            show C.degree ab.1.1 + D.degree ab.2.1 = l
            omega⟩, Subtype.ext ab.1.2⟩
        left_inv := fun x => rfl
        right_inv := fun ab => rfl }
    have := Matrix.rank_submatrix
      (blk C (j : ℤ) (j : ℤ) h ⊗ₖ blk D (l - (j : ℤ)) (l - (j : ℤ)) h') e e
    rw [rank_kron] at this
    rw [← this]
    rfl
  · rintro ⟨⟨a, b⟩, _⟩ ⟨⟨a', b'⟩, _⟩ hne
    apply Subtype.ext
    simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at hne
    have := hH a a' (left_ne_zero_of_mul hne)
    show C.degree a = C.degree a'
    omega

lemma homology_subsingleton (C : BasedBinaryComplex) (i : ℤ)
    (hi : i ∉ Finset.univ.image C.degree) : Subsingleton (Homology C i) := by
  have hE : IsEmpty (Basis C i) :=
    ⟨fun a => hi (Finset.mem_image.mpr ⟨a.1, Finset.mem_univ _, a.2⟩)⟩
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg _ (Subtype.ext (funext fun a => hE.elim a))

lemma tensor_subsingleton_left {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Subsingleton V] :
    Subsingleton (TensorProduct (ZMod 2) V W) := by
  have key : ∀ x : TensorProduct (ZMod 2) V W, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

lemma directSum_fin (S : Finset ℤ) (M : ℤ → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module (ZMod 2) (M i)] [∀ i, FiniteDimensional (ZMod 2) (M i)]
    (hS : ∀ i ∉ S, Subsingleton (M i)) :
    FiniteDimensional (ZMod 2) (DirectSum ℤ M) ∧ Module.Free (ZMod 2) (DirectSum ℤ M) ∧
      Module.finrank (ZMod 2) (DirectSum ℤ M) = ∑ j : S, Module.finrank (ZMod 2) (M j) := by
  let Φ : DirectSum ℤ M →ₗ[ZMod 2] (∀ j : S, M j) :=
    LinearMap.pi (fun j => DirectSum.component (ZMod 2) ℤ M j)
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro f g hfg
      refine DirectSum.ext fun i => ?_
      by_cases hi : i ∈ S
      · exact congr_fun hfg ⟨i, hi⟩
      · haveI := hS i hi
        exact Subsingleton.elim _ _
    · intro g
      refine ⟨∑ i : S, DirectSum.lof (ZMod 2) ℤ M i (g i), funext fun j => ?_⟩
      simp only [Φ, LinearMap.pi_apply, map_sum]
      rw [Finset.sum_eq_single j]
      · exact DirectSum.component.lof_self _ _ _
      · intro i _ hij
        rw [DirectSum.component.of, dif_neg]
        exact fun h => hij (Subtype.ext h)
      · intro h; exact absurd (Finset.mem_univ _) h
  let e := LinearEquiv.ofBijective Φ hΦ
  have : FiniteDimensional (ZMod 2) (DirectSum ℤ M) := Module.Finite.equiv e.symm
  exact ⟨this, Module.Free.of_equiv e.symm, by rw [e.finrank_eq, Module.finrank_pi_fintype]⟩

lemma one_tensor_eq (C D : BasedBinaryComplex) :
    ((1 : Matrix C.Cell C.Cell (ZMod 2)) ⊗ₖ (1 : Matrix D.Cell D.Cell (ZMod 2))) =
      (1 : Matrix (tensorComplex C D).Cell (tensorComplex C D).Cell (ZMod 2)) := by
  rw [kron_one_one' C D]
  exact congrArg (fun inst : DecidableEq (C.Cell × D.Cell) =>
    (@OfNat.ofNat (Matrix (C.Cell × D.Cell) (C.Cell × D.Cell) (ZMod 2)) 1
      (@One.toOfNat1 _ (@Matrix.one _ (ZMod 2) inst _ _)))) (Subsingleton.elim _ _)

end KunnethAux

open QAlgorithms.Papers.Independent.Independent1.P06 QAlgorithms in
theorem solution (C D : Surgery.BasedBinaryComplex) (l : ℤ) :
    Nonempty (Surgery.Homology (Surgery.tensorComplex C D) l ≃ₗ[F2]
      DirectSum ℤ (fun i : ℤ => TensorProduct F2
        (Surgery.Homology C i) (Surgery.Homology D (l - i)))) := by
  obtain ⟨s, hs, hss, hdsd⟩ := KunnethAux.exists_splitting C
  obtain ⟨s', hs', hss', hdsd'⟩ := KunnethAux.exists_splitting D
  have P := KunnethAux.harmonic_props C s hs hss hdsd
  have P' := KunnethAux.harmonic_props D s' hs' hss' hdsd'
  dsimp only at P P'
  generalize hh : 1 + C.differential * s + s * C.differential = h at P
  generalize hh' : 1 + D.differential * s' + s' * D.differential = h' at P'
  obtain ⟨hH, dh, hd, hhh⟩ := P
  obtain ⟨hH', dh', hd', hhh'⟩ := P'
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := KunnethAux.tensor_props C D s h s' h' hs hs' hH hH'
    hh.symm hh'.symm dh hd hhh dh' hd' hhh'
  have t3' := t3
  rw [← KunnethAux.kron_one_one' C D, KunnethAux.one_tensor_eq C D] at t3'
  have key := KunnethAux.finrank_homology_eq (Surgery.tensorComplex C D) (h ⊗ₖ h')
    ((s ⊗ₖ 1) + (h ⊗ₖ s')) t1 t2 t3' t4 t5 t6 l
  have hC := fun i => KunnethAux.finrank_homology_eq C h s hH hs hh.symm dh hd hhh i
  have hD := fun i => KunnethAux.finrank_homology_eq D h' s' hH' hs' hh'.symm dh' hd' hhh' i
  have E2 := KunnethAux.rank_block_kron C D l h h' hH
  obtain ⟨hfin, hfree, hF⟩ := @KunnethAux.directSum_fin (Finset.univ.image C.degree)
    (fun i : ℤ => TensorProduct F2 (Surgery.Homology C i) (Surgery.Homology D (l - i)))
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun i hi => by
      haveI := KunnethAux.homology_subsingleton C i hi
      exact KunnethAux.tensor_subsingleton_left)
  haveI : ∀ i, AddCommGroup
      (TensorProduct F2 (Surgery.Homology C i) (Surgery.Homology D (l - i))) :=
    fun _ => inferInstance
  haveI := hfin
  haveI := hfree
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  rw [key, hF]
  refine E2.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Module.finrank_tensorProduct, hC, hD]
