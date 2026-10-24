-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:00:00.748342+00:00
-- url     : https://prove2.me/submissions/d596bf30-cd26-49cc-b555-0253b9af64d0

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

-- ===== HA

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! isometric padding along an injective index map -/

section pad
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
  [DecidableEq K]

def Vm (e : I → J) : Matrix J I ℂ := Matrix.of fun j i => if j = e i then 1 else 0

def pad (e : I → J) (X : Matrix I I ℂ) : Matrix J J ℂ := Vm e * X * (Vm e)ᴴ

lemma Vm_iso {e : I → J} (he : Function.Injective e) : (Vm e)ᴴ * Vm e = 1 := by
  ext i i'
  simp only [Vm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (e i)]
  · by_cases h : i = i'
    · subst h; simp
    · simp [h, he.ne h]
  · intro j _ hj; simp [hj]
  · simp

lemma pad_apply (e : I → J) (X : Matrix I I ℂ) (j j' : J) :
    pad e X j j' = ∑ i, ∑ i', (if j = e i then 1 else 0) * X i i' * (if j' = e i' then 1 else 0) := by
  simp only [pad, Vm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma pad_ee {e : I → J} (he : Function.Injective e) (X : Matrix I I ℂ) (i i' : I) :
    pad e X (e i) (e i') = X i i' := by
  rw [pad_apply, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i']
    · simp
    · intro b _ hb; simp [(he.ne hb).symm]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    have : e i ≠ e b := he.ne (Ne.symm hb)
    simp [this]
  · simp

lemma pad_out {e : I → J} (X : Matrix I I ℂ) (j j' : J)
    (h : j ∉ Set.range e ∨ j' ∉ Set.range e) : pad e X j j' = 0 := by
  rw [pad_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
  rcases h with h | h
  · have : j ≠ e i := fun hh => h ⟨i, hh.symm⟩
    simp [this]
  · have : j' ≠ e i' := fun hh => h ⟨i', hh.symm⟩
    simp [this]

lemma pad_ext {e : I → J} (he : Function.Injective e) {X : Matrix I I ℂ} {Z : Matrix J J ℂ}
    (h1 : ∀ i i', Z (e i) (e i') = X i i')
    (h2 : ∀ j j', (j ∉ Set.range e ∨ j' ∉ Set.range e) → Z j j' = 0) : Z = pad e X := by
  ext j j'
  by_cases hj : j ∈ Set.range e
  · by_cases hj' : j' ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj; obtain ⟨i', rfl⟩ := hj'
      rw [h1, pad_ee he]
    · rw [h2 _ _ (Or.inr hj'), pad_out _ _ _ (Or.inr hj')]
  · rw [h2 _ _ (Or.inl hj), pad_out _ _ _ (Or.inl hj)]

lemma pad_ext_surj {e : I → J} (he : Function.Bijective e) {X : Matrix I I ℂ} {Z : Matrix J J ℂ}
    (h1 : ∀ i i', Z (e i) (e i') = X i i') : Z = pad e X :=
  pad_ext he.1 h1 fun j j' h => by
    rcases h with h | h
    · exact absurd (he.2 j) (by simpa [Set.mem_range] using h)
    · exact absurd (he.2 j') (by simpa [Set.mem_range] using h)

lemma pad_pad {e : I → J} {f : J → K} (he : Function.Injective e) (hf : Function.Injective f)
    (X : Matrix I I ℂ) : pad f (pad e X) = pad (f ∘ e) X :=
  pad_ext (hf.comp he) (fun i i' => by simp only [Function.comp, pad_ee hf, pad_ee he])
    fun j j' h => by
      by_cases hj : j ∈ Set.range f
      · by_cases hj' : j' ∈ Set.range f
        · obtain ⟨a, rfl⟩ := hj; obtain ⟨a', rfl⟩ := hj'
          rw [pad_ee hf]
          refine pad_out _ _ _ ?_
          rcases h with h | h
          · left; rintro ⟨i, rfl⟩; exact h ⟨i, rfl⟩
          · right; rintro ⟨i, rfl⟩; exact h ⟨i, rfl⟩
        · exact pad_out _ _ _ (Or.inr hj')
      · exact pad_out _ _ _ (Or.inl hj)

lemma trace_pad {e : I → J} (he : Function.Injective e) (X : Matrix I I ℂ) :
    (pad e X).trace = X.trace := by
  rw [pad, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Vm_iso he, Matrix.one_mul]

lemma pad_psd (e : I → J) {X : Matrix I I ℂ} (hX : X.PosSemidef) : (pad e X).PosSemidef :=
  hX.mul_mul_conjTranspose_same _

lemma pad_density {e : I → J} (he : Function.Injective e) {X : Matrix I I ℂ}
    (hX : IsDensityMatrix X) : IsDensityMatrix (pad e X) :=
  ⟨pad_psd e hX.1, by rw [trace_pad he, hX.2]⟩

lemma effectProb_pad {e : I → J} (he : Function.Injective e) (T Z : Matrix I I ℂ) :
    effectProb (pad e T) (pad e Z) = effectProb T Z := by
  unfold effectProb pad
  congr 1
  have h := Vm_iso he
  calc (Vm e * T * (Vm e)ᴴ * (Vm e * Z * (Vm e)ᴴ)).trace
      = (Vm e * (T * ((Vm e)ᴴ * Vm e) * Z) * (Vm e)ᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (T * Z).trace := by
        rw [h, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

lemma one_sub_pad {e : I → J} (he : Function.Injective e) (T : Matrix I I ℂ) :
    (1 - pad e T) = pad e (1 - T) + (1 - Vm e * (Vm e)ᴴ) := by
  simp only [pad, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

lemma proj_psd {e : I → J} (he : Function.Injective e) :
    (1 - Vm e * (Vm e)ᴴ : Matrix J J ℂ).PosSemidef := by
  have hP : (1 - Vm e * (Vm e)ᴴ : Matrix J J ℂ) =
      (1 - Vm e * (Vm e)ᴴ)ᴴ * (1 - Vm e * (Vm e)ᴴ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    have : Vm e * (Vm e)ᴴ * (Vm e * (Vm e)ᴴ) = Vm e * (Vm e)ᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Vm e)ᴴ, Vm_iso he, Matrix.one_mul]
    rw [this]; abel
  rw [hP]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma pad_effect {e : I → J} (he : Function.Injective e) {T : Matrix I I ℂ} (hT : IsEffect T) :
    IsEffect (pad e T) :=
  ⟨pad_psd e hT.1, by rw [one_sub_pad he]; exact (pad_psd e hT.2).add (proj_psd he)⟩

lemma effectProb_one_sub_pad {e : I → J} (he : Function.Injective e) (T Z : Matrix I I ℂ) :
    effectProb (1 - pad e T) (pad e Z) = effectProb (1 - T) Z := by
  have h1 : (1 : Matrix J J ℂ) - pad e T = pad e (1 - T) + (1 - Vm e * (Vm e)ᴴ) := one_sub_pad he T
  have h0 : effectProb (1 - Vm e * (Vm e)ᴴ : Matrix J J ℂ) (pad e Z) = 0 := by
    unfold effectProb pad
    have : (1 - Vm e * (Vm e)ᴴ) * (Vm e * Z * (Vm e)ᴴ) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_assoc (Vm e) (Vm e)ᴴ, Vm_iso he, Matrix.mul_one, sub_self]
    rw [this]; simp
  rw [h1]
  unfold effectProb at *
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, h0, add_zero]
  exact effectProb_pad he _ _

/-- tests transport along isometric paddings. -/
lemma testing_pad {e : I → J} (he : Function.Injective e) (S : Set (Matrix I I ℂ))
    (S' : Set (Matrix J J ℂ)) (hS : ∀ Y ∈ S', ∃ Z ∈ S, Y = pad e Z) (σ : Matrix I I ℂ)
    (eps : ℝ) : testingBits S σ eps ≤ testingBits S' (pad e σ) eps := by
  unfold testingBits
  refine iSup_le fun T => ?_
  obtain ⟨T, hTe, hT1⟩ := T
  refine le_iSup_of_le ⟨pad e T, pad_effect he hTe, ?_⟩ (le_of_eq ?_)
  · intro ρ hρ
    obtain ⟨Z, hZ, rfl⟩ := hS ρ hρ
    rw [effectProb_one_sub_pad he]; exact hT1 Z hZ
  · simp only [effectProb_pad he]

end pad

section sq
open scoped Matrix.Norms.L2Operator MatrixOrder
set_option backward.isDefEq.respectTransparency false in
lemma psd_factor {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (h : X.PosSemidef) :
    ∃ B : Matrix n n ℂ, X = Bᴴ * B := by
  have h0 : 0 ≤ X := h.nonneg
  refine ⟨CFC.sqrt X, ?_⟩
  have hs : IsSelfAdjoint (CFC.sqrt X) := (CFC.sqrt_nonneg X).isSelfAdjoint
  rw [← Matrix.star_eq_conjTranspose, hs.star_eq, CFC.sqrt_mul_sqrt_self X h0]
end sq

end X4H

end

-- ===== HB

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! copies over an arbitrary finite index type -/

section copies
variable {I : Type*} [Fintype I] [DecidableEq I]

def copiesT (V : Type*) [Fintype V] (X : Matrix I I ℂ) : Matrix (V → I) (V → I) ℂ :=
  Matrix.of fun x y => ∏ v, X (x v) (y v)

lemma copies_eq (m : ℕ) (X : Matrix I I ℂ) : copies m X = copiesT (Fin m) X := rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma copies_pad {J : Type*} [Fintype J] [DecidableEq J] {e : I → J}
    (he : Function.Injective e) (X : Matrix I I ℂ) :
    copiesT V (pad e X) = pad (fun x v => e (x v)) (copiesT V X) := by
  have hinj : Function.Injective (fun (x : V → I) v => e (x v)) :=
    fun x y h => funext fun v => he (congrFun h v)
  refine pad_ext hinj (fun x y => by simp [copiesT, pad_ee he]) fun y y' h => ?_
  have key : ∀ z : V → J, z ∉ Set.range (fun (x : V → I) v => e (x v)) → ∃ v, z v ∉ Set.range e := by
    intro z hz
    by_contra hc
    push Not at hc
    exact hz ⟨fun v => (hc v).choose, funext fun v => (hc v).choose_spec⟩
  simp only [copiesT, Matrix.of_apply]
  rcases h with h | h
  · obtain ⟨v, hv⟩ := key y h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (pad_out _ _ _ (Or.inl hv))
  · obtain ⟨v, hv⟩ := key y' h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (pad_out _ _ _ (Or.inr hv))

/-- reindexing `V × U ≃ W` for plain functions. -/
def eW {U W : Type*} (φ : V × U ≃ W) (α : Type*) : (V → U → α) ≃ (W → α) :=
  (Equiv.curry V U α).symm.trans (Equiv.arrowCongr φ (Equiv.refl α))

lemma eW_apply {U W α : Type*} (φ : V × U ≃ W) (g : V → U → α) (w : W) :
    eW φ α g w = g (φ.symm w).1 (φ.symm w).2 := rfl

lemma eW_symm_apply {U W α : Type*} (φ : V × U ≃ W) (c : W → α) (v : V) (u : U) :
    (eW φ α).symm c v u = c (φ (v, u)) := rfl

lemma copies_copies {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (φ : V × U ≃ W) (Y : Matrix I I ℂ) :
    copiesT V (copiesT U Y) = pad (eW φ I).symm (copiesT W Y) := by
  refine pad_ext_surj (eW φ I).symm.bijective fun c c' => ?_
  simp only [copiesT, Matrix.of_apply, eW_symm_apply]
  rw [← Fintype.prod_prod_type' (f := fun v u => Y (c (φ (v, u))) (c' (φ (v, u))))]
  exact φ.prod_comp (fun w => Y (c w) (c' w))

lemma copies_psd {X : Matrix I I ℂ} (hX : X.PosSemidef) : (copiesT V X).PosSemidef := by
  obtain ⟨B, rfl⟩ := psd_factor hX
  have : copiesT V (Bᴴ * B) = (copiesT V B)ᴴ * copiesT V B := by
    ext x y
    simp only [copiesT, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_mul_distrib, star_prod]
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma copies_trace (X : Matrix I I ℂ) : (copiesT V X).trace = X.trace ^ Fintype.card V := by
  simp only [Matrix.trace, Matrix.diag, copiesT, Matrix.of_apply]
  rw [← Fintype.prod_sum (fun (_ : V) i => X i i), Finset.prod_const, Finset.card_univ]

lemma copies_density {X : Matrix I I ℂ} (hX : IsDensityMatrix X) : IsDensityMatrix (copiesT V X) :=
  ⟨copies_psd hX.1, by rw [copies_trace, hX.2, one_pow]⟩

end copies

/-! block outputs over an arbitrary finite set of uses -/

section outT
variable {r a b : ℕ}

abbrev RegT (U : Type*) (r a : ℕ) := (U → Fin r) × (U → Fin a)

def ker (Φ : Superop (Fin a) (Fin b)) (u u' : Fin a) (v v' : Fin b) : ℂ :=
  Φ (Matrix.single u u' 1) v v'

def outT (U : Type*) [Fintype U] [DecidableEq U] (Φ : Superop (Fin a) (Fin b)) (X : Mat (RegT U r a)) :
    Mat (RegT U r b) :=
  Matrix.of fun p q => ∑ x : U → Fin a, ∑ x' : U → Fin a,
    X (p.1, x) (q.1, x') * ∏ u, ker Φ (x u) (x' u) (p.2 u) (q.2 u)

lemma output_eq {k : ℕ} (Φ : Maps a b) (X : Mat (Reg r a k)) :
    output r k Φ X = outT (Fin k) (Φ : Superop (Fin a) (Fin b)) X := rfl

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W]

def blk (φ : V × U ≃ W) (r a : ℕ) (F : V → RegT U r a) : RegT W r a :=
  (eW φ _ (fun v => (F v).1), eW φ _ (fun v => (F v).2))

lemma blk_bij (φ : V × U ≃ W) (r a : ℕ) : Function.Bijective (blk φ r a) :=
  ((Equiv.arrowProdEquivProdArrow V (fun _ => U → Fin r) (fun _ => U → Fin a)).trans
    (Equiv.prodCongr (eW φ _) (eW φ _))).bijective

lemma outT_blk (φ : V × U ≃ W) (Φ : Superop (Fin a) (Fin b)) (X : Mat (RegT U r a)) :
    outT W Φ (pad (blk φ r a) (copiesT V X)) = pad (blk φ r b) (copiesT V (outT U Φ X)) := by
  refine pad_ext_surj (blk_bij φ r b) fun F F' => ?_
  simp only [outT, copiesT, Matrix.of_apply]
  rw [Fintype.prod_sum]
  simp only [Fintype.prod_sum]
  rw [← (eW φ (Fin a)).bijective.sum_comp]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← (eW φ (Fin a)).bijective.sum_comp]
  refine Finset.sum_congr rfl fun g' _ => ?_
  have h1 : ((blk φ r b F).1, eW φ (Fin a) g) = blk φ r a (fun v => ((F v).1, g v)) := rfl
  have h2 : ((blk φ r b F').1, eW φ (Fin a) g') = blk φ r a (fun v => ((F' v).1, g' v)) := rfl
  rw [h1, h2, pad_ee (blk_bij φ r a).1, Matrix.of_apply, Finset.prod_mul_distrib]
  congr 1
  refine (Fintype.prod_equiv φ.symm _
    (fun p : V × U => ker Φ (g p.1 p.2) (g' p.1 p.2) ((F p.1).2 p.2) ((F' p.1).2 p.2))
    (fun w => rfl)).trans ?_
  exact Fintype.prod_prod_type _

/-- reindexing `U ⊕ U' ≃ W` for plain functions. -/
def eS {U' : Type*} (φ : U ⊕ U' ≃ W) (α : Type*) : (U → α) × (U' → α) ≃ (W → α) :=
  (Equiv.sumArrowEquivProdArrow U U' α).symm.trans (Equiv.arrowCongr φ (Equiv.refl α))

lemma eS_inl {U' α : Type*} (φ : U ⊕ U' ≃ W) (g : U → α) (h : U' → α) (u : U) :
    eS φ α (g, h) (φ (Sum.inl u)) = g u := by simp [eS]

lemma eS_inr {U' α : Type*} (φ : U ⊕ U' ≃ W) (g : U → α) (h : U' → α) (u : U') :
    eS φ α (g, h) (φ (Sum.inr u)) = h u := by simp [eS]

variable {U' : Type*} [Fintype U'] [DecidableEq U']

def blk2 (φ : U ⊕ U' ≃ W) (r a : ℕ) (P : RegT U r a × RegT U' r a) : RegT W r a :=
  (eS φ _ (P.1.1, P.2.1), eS φ _ (P.1.2, P.2.2))

lemma blk2_bij (φ : U ⊕ U' ≃ W) (r a : ℕ) : Function.Bijective (blk2 φ r a) :=
  ((Equiv.prodProdProdComm _ _ _ _).trans (Equiv.prodCongr (eS φ _) (eS φ _))).bijective

lemma outT_sum (φ : U ⊕ U' ≃ W) (Φ : Superop (Fin a) (Fin b)) (X : Mat (RegT U r a))
    (Z : Mat (RegT U' r a)) :
    outT W Φ (pad (blk2 φ r a) (X ⊗ₖ Z)) = pad (blk2 φ r b) (outT U Φ X ⊗ₖ outT U' Φ Z) := by
  refine pad_ext_surj (blk2_bij φ r b) fun P P' => ?_
  simp only [outT, Matrix.kroneckerMap_apply, Matrix.of_apply, Finset.sum_mul_sum]
  rw [← (eS φ (Fin a)).bijective.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
  rw [← (eS φ (Fin a)).bijective.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g' _ => Finset.sum_congr rfl fun h' _ => ?_
  have h1 : ((blk2 φ r b P).1, eS φ (Fin a) (g, h)) = blk2 φ r a ((P.1.1, g), (P.2.1, h)) := rfl
  have h2 : ((blk2 φ r b P').1, eS φ (Fin a) (g', h')) =
    blk2 φ r a ((P'.1.1, g'), (P'.2.1, h')) := rfl
  rw [h1, h2, pad_ee (blk2_bij φ r a).1, Matrix.kroneckerMap_apply]
  rw [← φ.prod_comp, Fintype.prod_sum_type]
  simp only [blk2, eS_inl, eS_inr]
  ring

lemma trace_outT (Φ : Superop (Fin a) (Fin b))
    (hΦ : ∀ u u', ∑ v, ker Φ u u' v v = if u = u' then 1 else 0)
    (X : Mat (RegT U r a)) : (outT U Φ X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, outT, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have : ∀ x' : U → Fin a, ∑ y : U → Fin b, ∏ u, ker Φ (x u) (x' u) (y u) (y u) =
      if x = x' then 1 else 0 := by
    intro x'
    rw [← Fintype.prod_sum (fun u j => ker Φ (x u) (x' u) j j)]
    simp only [hΦ, Finset.prod_boole, Finset.mem_univ, true_implies, funext_iff, forall_const]
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma chan_trace {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] {Φ : Superop I K}
    (hΦ : IsChannel Φ) (A : Matrix I I ℂ) : (Φ A).trace = A.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := hΦ
  rw [hΦ, krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_comm _ (E _)ᴴ, ← Matrix.mul_assoc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

lemma chan_single {Φ : Superop (Fin a) (Fin b)} (hΦ : IsChannel Φ) (u u' : Fin a) :
    ∑ v, ker Φ u u' v v = if u = u' then 1 else 0 := by
  have := chan_trace hΦ (Matrix.single u u' 1)
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [ker, this, Matrix.single_apply]
  by_cases h : u = u'
  · simp [h]
  · simp [h, Ne.symm h]

end outT

/-! tests ignoring a tensor factor -/

section kron
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

lemma effectProb_kron (T Z : Matrix I I ℂ) (B : Matrix K K ℂ) (hB : B.trace = 1) :
    effectProb (T ⊗ₖ (1 : Matrix K K ℂ)) (Z ⊗ₖ B) = effectProb T Z := by
  unfold effectProb
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker, hB, mul_one]

lemma testing_kron (S : Set (Matrix I I ℂ)) (S' : Set (Matrix (I × K) (I × K) ℂ))
    (hS : ∀ Y ∈ S', ∃ Z ∈ S, ∃ B : Matrix K K ℂ, B.trace = 1 ∧ Y = Z ⊗ₖ B) (σ : Matrix I I ℂ)
    (B0 : Matrix K K ℂ) (hB0 : B0.trace = 1) (eps : ℝ) :
    testingBits S σ eps ≤ testingBits S' (σ ⊗ₖ B0) eps := by
  unfold testingBits
  refine iSup_le fun T => ?_
  obtain ⟨T, hTe, hT1⟩ := T
  have hsub : (1 : Matrix (I × K) (I × K) ℂ) - T ⊗ₖ (1 : Matrix K K ℂ) = (1 - T) ⊗ₖ 1 := by
    rw [← Matrix.one_kronecker_one, sub_eq_iff_eq_add, ← Matrix.add_kronecker, sub_add_cancel]
  refine le_iSup_of_le ⟨T ⊗ₖ (1 : Matrix K K ℂ), ⟨hTe.1.kronecker Matrix.PosSemidef.one, by
    rw [hsub]; exact hTe.2.kronecker Matrix.PosSemidef.one⟩, ?_⟩ (le_of_eq ?_)
  · intro ρ hρ
    obtain ⟨Z, hZ, B, hB, rfl⟩ := hS ρ hρ
    rw [hsub, effectProb_kron _ _ _ hB]; exact hT1 Z hZ
  · simp only [effectProb_kron _ _ _ hB0]

lemma kron_density {Z : Matrix I I ℂ} {B : Matrix K K ℂ} (hZ : IsDensityMatrix Z)
    (hB : IsDensityMatrix B) : IsDensityMatrix (Z ⊗ₖ B) :=
  ⟨hZ.1.kronecker hB.1, by rw [Matrix.trace_kronecker, hZ.2, hB.2, one_mul]⟩

end kron

end X4H

end

-- ===== HC

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section rates
variable {a b : ℕ}

lemma op_mono {g g' : ℕ → ℝ → ℝ≥0∞} (h : ∀ m eps, g m eps ≤ g' m eps) :
    operational g ≤ operational g' := by
  unfold operational
  exact liminf_le_liminf (Eventually.of_forall fun eps =>
    liminf_le_liminf (Eventually.of_forall fun m => h m eps))

lemma liminf_comp_ge {g : ℕ → ℝ≥0∞} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    liminf g atTop ≤ liminf (fun m => g (φ m)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  exact le_liminf_of_le (by isBoundedDefault)
    ((hφ.eventually (eventually_lt_of_lt_liminf hc)).mono fun m h => h.le)

lemma op_sub {g g' : ℕ → ℝ → ℝ≥0∞} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (h : ∀ m eps, g (φ m) eps ≤ g' m eps) : operational g ≤ operational g' := by
  unfold operational
  exact liminf_le_liminf (Eventually.of_forall fun eps =>
    (liminf_comp_ge (g := fun n => g n eps) hφ).trans
      (liminf_le_liminf (Eventually.of_forall fun m => h m eps)))

lemma rate_set {r k : ℕ} (R : Set (Maps a b)) (N : Maps a b) {P P' : Set (Mat (Reg r a k))}
    (hP : P ⊆ P') (m : ℕ) (eps : ℝ) :
    blockRate r R N k P m eps ≤ blockRate r R N k P' m eps := by
  unfold blockRate
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  exact le_iSup (fun Y : P' => testingBits {Y' | ∃ Phi ∈ R, Y' = copies (m + 1) (output r k Phi Y.1)}
    (copies (m + 1) (output r k N Y.1)) eps) ⟨X.1, hP X.2⟩

lemma adm_ps {r k : ℕ} : admissible r a k .product ⊆ admissible r a k .separable := by
  rintro X ⟨hX, tau, htau, rfl⟩
  exact ⟨hX, 1, fun _ => 1, fun _ => tau, fun _ => zero_le_one, by simp, fun _ i => htau i,
    by simp⟩

lemma adm_su {r k : ℕ} : admissible r a k .separable ⊆ admissible r a k .unrestricted :=
  fun _ hX => ⟨hX.1, trivial⟩

end rates

/-! reference padding `r = 1 ↦ r = a` -/

section ref
variable {a b k : ℕ}

def eR (ha : 0 < a) (k c : ℕ) : Reg 1 c k → Reg a c k := fun p => (fun _ => ⟨0, ha⟩, p.2)

lemma eR_inj (ha : 0 < a) (k c : ℕ) : Function.Injective (eR ha k c) := fun p q h =>
  Prod.ext (Subsingleton.elim _ _) (by have := congrArg Prod.snd h; exact this)

lemma eR_range (ha : 0 < a) {c : ℕ} (j : Reg a c k) :
    j ∈ Set.range (eR ha k c) ↔ j.1 = fun _ => ⟨0, ha⟩ :=
  ⟨by rintro ⟨p, rfl⟩; rfl, fun h => ⟨(fun _ => 0, j.2), Prod.ext h.symm rfl⟩⟩

lemma out_eR (ha : 0 < a) (Φ : Maps a b) (X : Mat (Reg 1 a k)) :
    output a k Φ (pad (eR ha k a) X) = pad (eR ha k b) (output 1 k Φ X) := by
  rw [output_eq, output_eq]
  refine pad_ext (eR_inj ha k b) (fun p q => ?_) (fun j j' h => ?_)
  · simp only [outT, Matrix.of_apply]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    rw [show ((eR ha k b p).1, x) = eR ha k a (p.1, x) from rfl,
      show ((eR ha k b q).1, x') = eR ha k a (q.1, x') from rfl, pad_ee (eR_inj ha k a)]
    rfl
  · simp only [outT, Matrix.of_apply]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x' _ => ?_
    rw [pad_out, zero_mul]
    rcases h with h | h
    · left; rw [eR_range] at h ⊢; exact h
    · right; rw [eR_range] at h ⊢; exact h

def e1 (ha : 0 < a) : Fin 1 × Fin a → Fin a × Fin a := fun p => (⟨0, ha⟩, p.2)

lemma e1_inj (ha : 0 < a) : Function.Injective (e1 ha) := fun p q h =>
  Prod.ext (Subsingleton.elim _ _) (by have := congrArg Prod.snd h; exact this)

lemma pp_pad (ha : 0 < a) (tau : Fin k → Mat (Fin 1 × Fin a)) :
    pad (eR ha k a) (productProbe tau) = productProbe (fun i => pad (e1 ha) (tau i)) := by
  symm
  refine pad_ext (eR_inj ha k a) (fun p q => ?_) (fun j j' h => ?_)
  · simp only [productProbe, Matrix.of_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show ((eR ha k a p).1 i, (eR ha k a p).2 i) = e1 ha (p.1 i, p.2 i) from rfl,
      show ((eR ha k a q).1 i, (eR ha k a q).2 i) = e1 ha (q.1 i, q.2 i) from rfl,
      pad_ee (e1_inj ha)]
  · have key : ∀ jj : Reg a a k, jj ∉ Set.range (eR ha k a) →
        ∃ i, (jj.1 i, jj.2 i) ∉ Set.range (e1 ha) := by
      intro jj hj
      rw [eR_range] at hj
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
      exact ⟨i, by rintro ⟨p, hp⟩; exact hi (congrArg Prod.fst hp).symm⟩
    simp only [productProbe, Matrix.of_apply]
    rcases h with h | h
    · obtain ⟨i, hi⟩ := key j h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (pad_out _ _ _ (Or.inl hi))
    · obtain ⟨i, hi⟩ := key j' h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (pad_out _ _ _ (Or.inr hi))

lemma pad_sum_smul {I J ι : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype ι] (e : I → J) (w : ι → ℂ) (P : ι → Matrix I I ℂ) :
    pad e (∑ j, w j • P j) = ∑ j, w j • pad e (P j) := by
  simp only [pad, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma adm_pad (ha : 0 < a) {c : Correlation} {X : Mat (Reg 1 a k)}
    (hX : X ∈ admissible 1 a k c) : pad (eR ha k a) X ∈ admissible a a k c := by
  refine ⟨pad_density (eR_inj ha k a) hX.1, ?_⟩
  obtain ⟨-, h⟩ := hX
  cases c with
  | unrestricted => trivial
  | product =>
    obtain ⟨tau, htau, rfl⟩ := h
    exact ⟨fun i => pad (e1 ha) (tau i), fun i => pad_density (e1_inj ha) (htau i), pp_pad ha tau⟩
  | separable =>
    obtain ⟨q, w, tau, h0, h1, ht, rfl⟩ := h
    refine ⟨q, w, fun j i => pad (e1 ha) (tau j i), h0, h1,
      fun j i => pad_density (e1_inj ha) (ht j i), ?_⟩
    rw [pad_sum_smul]
    simp only [pp_pad]

lemma rate_ref (ha : 0 < a) (R : Set (Maps a b)) (N : Maps a b) (c : Correlation) (m : ℕ)
    (eps : ℝ) :
    blockRate 1 R N k (admissible 1 a k c) m eps ≤ blockRate a R N k (admissible a a k c) m eps := by
  unfold blockRate
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  refine le_iSup_of_le (⟨pad (eR ha k a) X.1, adm_pad ha X.2⟩ : admissible a a k c) ?_
  have hE : Function.Injective (fun (x : Fin (m + 1) → Reg 1 b k) v => eR ha k b (x v)) :=
    fun x y h => funext fun v => eR_inj ha k b (congrFun h v)
  have key : ∀ Φ : Maps a b, copies (m + 1) (output a k Φ (pad (eR ha k a) X.1)) =
      pad (fun (x : Fin (m + 1) → Reg 1 b k) v => eR ha k b (x v))
        (copies (m + 1) (output 1 k Φ X.1)) := fun Φ => by
    rw [out_eR, copies_eq, copies_pad (eR_inj ha k b)]; rfl
  simp only
  rw [key N]
  refine testing_pad hE _ _ ?_ _ _
  rintro Y ⟨Φ, hΦ, rfl⟩
  exact ⟨_, ⟨Φ, hΦ, rfl⟩, key Φ⟩

lemma exp_ref (ha : 0 < a) (R : Set (Maps a b)) (N : Maps a b) (c : Correlation) :
    blockExponent 1 R N k c ≤ blockExponent a R N k c :=
  op_mono fun m eps => rate_ref ha R N c m eps

end ref

/-! regrouping `ℓ` blocks of `k` uses -/

section regroup
variable {a b k r : ℕ}

lemma rate_blk (R : Set (Maps a b)) (N : Maps a b) {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) (eps : ℝ) :
    blockRate r R N k (admissible r a k .unrestricted) (ℓ * (m + 1) - 1) eps ≤
      blockRate r R N (ℓ * k) (admissible r a (ℓ * k) .unrestricted) m eps := by
  set n := ℓ * (m + 1) - 1 with hn0
  have hn : n + 1 = (m + 1) * ℓ := by
    have : 1 ≤ ℓ * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [hn0, Nat.sub_add_cancel this, mul_comm]
  have hd : k * (n + 1) = ℓ * k * (m + 1) := by rw [hn]; ring
  unfold blockRate
  rw [hd]
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  let φ : Fin ℓ × Fin k ≃ Fin (ℓ * k) := finProdFinEquiv
  let ψ : Fin (m + 1) × Fin ℓ ≃ Fin (n + 1) := finProdFinEquiv.trans (finCongr hn.symm)
  have hX' : pad (blk φ r a) (copiesT (Fin ℓ) X.1) ∈ admissible r a (ℓ * k) .unrestricted :=
    ⟨pad_density (blk_bij φ r a).1 (copies_density X.2.1), trivial⟩
  refine le_iSup_of_le (⟨_, hX'⟩ : admissible r a (ℓ * k) .unrestricted) ?_
  have hE1 : Function.Injective (fun (x : Fin (m + 1) → Fin ℓ → Reg r b k) v => blk φ r b (x v)) :=
    fun x y h => funext fun v => (blk_bij φ r b).1 (congrFun h v)
  have hE : Function.Injective
      ((fun (x : Fin (m + 1) → Fin ℓ → Reg r b k) v => blk φ r b (x v)) ∘
        (eW ψ (Reg r b k)).symm) := hE1.comp (eW ψ _).symm.injective
  have key : ∀ Φ : Maps a b,
      copies (m + 1) (output r (ℓ * k) Φ (pad (blk φ r a) (copiesT (Fin ℓ) X.1))) =
      pad ((fun (x : Fin (m + 1) → Fin ℓ → Reg r b k) v => blk φ r b (x v)) ∘
        (eW ψ (Reg r b k)).symm) (copies (n + 1) (output r k Φ X.1)) := fun Φ => by
    rw [output_eq, outT_blk, ← output_eq, copies_eq, copies_pad (blk_bij φ r b).1,
      copies_copies ψ, pad_pad (eW ψ _).symm.injective hE1, copies_eq]
  simp only
  rw [key N]
  refine testing_pad hE _ _ ?_ _ _
  rintro Y ⟨Φ, hΦ, rfl⟩
  exact ⟨_, ⟨Φ, hΦ, rfl⟩, key Φ⟩

lemma exp_blk (R : Set (Maps a b)) (N : Maps a b) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    blockExponent r R N k .unrestricted ≤ blockExponent r R N (ℓ * k) .unrestricted := by
  refine op_sub (φ := fun m => ℓ * (m + 1) - 1) ?_ fun m eps => rate_blk R N hℓ m eps
  refine tendsto_atTop_mono (fun m => ?_) tendsto_id
  have : m + 1 ≤ ℓ * (m + 1) := Nat.le_mul_of_pos_left _ hℓ
  simp only [id]; omega

end regroup

end X4H

end

-- ===== HD

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section arb
variable {a b k r : ℕ}

lemma vv_density {I : Type*} [Fintype I] [DecidableEq I] (p : I) :
    IsDensityMatrix (Matrix.vecMulVec (Pi.single p (1 : ℂ)) (star (Pi.single p (1 : ℂ)))) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  simp [Matrix.trace, Matrix.vecMulVec_apply, Pi.single_apply]

lemma num_le {R : Set (Maps a b)} {N : Maps a b} (h : Setting R N) (hr : 0 < r) {n q : ℕ}
    (hq : (q + 1) * k ≤ n + 1) (eps : ℝ) :
    (⨆ X : admissible r a k .unrestricted, testingBits
        {Y | ∃ Phi ∈ R, Y = copies (q + 1) (output r k Phi X.1)}
        (copies (q + 1) (output r k N X.1)) eps) ≤
      (⨆ X : admissible r a (n + 1) .unrestricted, testingBits
        {Y | ∃ Phi ∈ R, Y = output r (n + 1) Phi X.1} (output r (n + 1) N X.1) eps) := by
  refine iSup_le fun X => ?_
  obtain ⟨ha, -, -, -, -, hR, hN, -⟩ := h
  set s := n + 1 - (q + 1) * k
  have hN' : (q + 1) * k + s = n + 1 := by omega
  let φ1 : Fin (q + 1) × Fin k ≃ Fin ((q + 1) * k) := finProdFinEquiv
  let φ2 : Fin ((q + 1) * k) ⊕ Fin s ≃ Fin (n + 1) := finSumFinEquiv.trans (finCongr hN')
  let p0 : RegT (Fin s) r a := (fun _ => ⟨0, hr⟩, fun _ => ⟨0, ha⟩)
  let ω : Mat (RegT (Fin s) r a) :=
    Matrix.vecMulVec (Pi.single p0 (1 : ℂ)) (star (Pi.single p0 (1 : ℂ)))
  have hω : IsDensityMatrix ω := vv_density p0
  let X1 := pad (blk φ1 r a) (copiesT (Fin (q + 1)) X.1)
  have hX' : pad (blk2 φ2 r a) (X1 ⊗ₖ ω) ∈ admissible r a (n + 1) .unrestricted :=
    ⟨pad_density (blk2_bij φ2 r a).1 (kron_density
      (pad_density (blk_bij φ1 r a).1 (copies_density X.2.1)) hω), trivial⟩
  refine le_iSup_of_le (⟨_, hX'⟩ : admissible r a (n + 1) .unrestricted) ?_
  have key : ∀ Φ : Maps a b, output r (n + 1) Φ (pad (blk2 φ2 r a) (X1 ⊗ₖ ω)) =
      pad (blk2 φ2 r b) (pad (blk φ1 r b) (copies (q + 1) (output r k Φ X.1)) ⊗ₖ
        outT (Fin s) (Φ : Superop (Fin a) (Fin b)) ω) := fun Φ => by
    rw [output_eq, outT_sum, outT_blk]; rfl
  have htr : ∀ Φ : Maps a b, IsChannel (Φ : Superop (Fin a) (Fin b)) →
      (outT (Fin s) (Φ : Superop (Fin a) (Fin b)) ω).trace = 1 := fun Φ hΦ => by
    rw [trace_outT _ (chan_single hΦ), hω.2]
  simp only
  rw [key N]
  refine le_trans (testing_pad (blk_bij φ1 r b).1 _
    {Y | ∃ Phi ∈ R, Y = pad (blk φ1 r b) (copies (q + 1) (output r k Phi X.1))} ?_ _ eps) ?_
  · rintro Y ⟨Φ, hΦ, rfl⟩; exact ⟨_, ⟨Φ, hΦ, rfl⟩, rfl⟩
  refine le_trans (testing_kron _
    {Y | ∃ Phi ∈ R, Y = pad (blk φ1 r b) (copies (q + 1) (output r k Phi X.1)) ⊗ₖ
        outT (Fin s) (Phi : Superop (Fin a) (Fin b)) ω} ?_ _ _ (htr N hN) eps) ?_
  · rintro Y ⟨Φ, hΦ, rfl⟩; exact ⟨_, ⟨Φ, hΦ, rfl⟩, _, htr Φ (hR Φ hΦ), rfl⟩
  refine testing_pad (blk2_bij φ2 r b).1 _ _ ?_ _ eps
  rintro Y ⟨Φ, hΦ, rfl⟩; exact ⟨_, ⟨Φ, hΦ, rfl⟩, key Φ⟩

lemma asym (hk : 0 < k) (T S : ℕ → ℝ≥0∞) (hTS : ∀ n q, (q + 1) * k ≤ n + 1 → T q ≤ S n) :
    liminf (fun m => T m / ((k * (m + 1) : ℕ) : ℝ≥0∞)) atTop ≤
      liminf (fun n => S n / ((n + 1 : ℕ) : ℝ≥0∞)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun δ hδ => ?_
  refine le_liminf_of_le (by isBoundedDefault) ?_
  let qf : ℕ → ℕ := fun n => (n + 1) / k - 1
  have hq : Tendsto qf atTop atTop := by
    refine tendsto_atTop_atTop.2 fun B => ⟨(B + 1) * k, fun n hn => ?_⟩
    have : B + 1 ≤ (n + 1) / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
    simp only [qf]; omega
  have h1 := hq.eventually (eventually_lt_of_lt_liminf hc)
  have hδt : δ ≠ ⊤ := ne_top_of_lt (hδ.trans ENNReal.one_lt_top)
  set t := δ.toReal with ht
  have ht1 : t < 1 := by
    have := (ENNReal.toReal_lt_toReal hδt ENNReal.one_ne_top).2 hδ
    simpa [ht] using this
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((k : ℝ) / (1 - t))
  have h2 : ∀ᶠ n in atTop, N0 ≤ n ∧ k ≤ n + 1 :=
    (eventually_ge_atTop (N0 + k)).mono fun n hn => ⟨by omega, by omega⟩
  filter_upwards [h1, h2] with n h1 h2
  obtain ⟨hn0, hkn⟩ := h2
  have hQ : qf n + 1 = (n + 1) / k := by
    have : 1 ≤ (n + 1) / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
    simp only [qf]; omega
  have hqk : (qf n + 1) * k ≤ n + 1 := by rw [hQ]; exact Nat.div_mul_le_self _ _
  -- real inequality δ (n+1) ≤ k (q+1)
  have hreal : t * ((n + 1 : ℕ) : ℝ) ≤ ((k * (qf n + 1) : ℕ) : ℝ) := by
    have hdm := Nat.div_add_mod (n + 1) k
    have hmod := Nat.mod_lt (n + 1) hk
    rw [hQ]
    have e1 : ((n + 1 : ℕ) : ℝ) = (k * ((n + 1) / k) : ℕ) + ((n + 1) % k : ℕ) := by
      rw [← Nat.cast_add, hdm]
    have e2 : (((n + 1) % k : ℕ) : ℝ) ≤ k := by exact_mod_cast hmod.le
    have hpos : 0 < 1 - t := by linarith
    have e3 : (k : ℝ) < (1 - t) * ((n + 1 : ℕ) : ℝ) := by
      have : (k : ℝ) / (1 - t) < ((n + 1 : ℕ) : ℝ) := by
        refine hN0.trans_le ?_; push_cast; exact_mod_cast (by omega : N0 ≤ n + 1)
      rwa [div_lt_iff₀ hpos, mul_comm] at this
    nlinarith
  have h2' : δ * ((n + 1 : ℕ) : ℝ≥0∞) ≤ ((k * (qf n + 1) : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hδt, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul ht0]
    exact ENNReal.ofReal_le_ofReal hreal
  have hn1 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hn2 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc δ * c ≤ δ * (T (qf n) / ((k * (qf n + 1) : ℕ) : ℝ≥0∞)) := by gcongr
    _ ≤ T (qf n) / ((n + 1 : ℕ) : ℝ≥0∞) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_left_comm]
      gcongr _ * ?_
      have : δ ≤ ((k * (qf n + 1) : ℕ) : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        calc δ = δ * ((n + 1 : ℕ) : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
              rw [mul_assoc, ENNReal.mul_inv_cancel hn1 hn2, mul_one]
          _ ≤ _ := by gcongr
      calc δ * ((k * (qf n + 1) : ℕ) : ℝ≥0∞)⁻¹
          ≤ ((k * (qf n + 1) : ℕ) : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
              ((k * (qf n + 1) : ℕ) : ℝ≥0∞)⁻¹ := by gcongr
        _ ≤ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [mul_comm, ← mul_assoc]
          exact mul_le_of_le_one_left' (ENNReal.inv_mul_le_one _)
    _ ≤ S n / ((n + 1 : ℕ) : ℝ≥0∞) := ENNReal.div_le_div_right (hTS n _ hqk) _

lemma exp_arb {R : Set (Maps a b)} {N : Maps a b} (h : Setting R N) (hr : 0 < r) (hk : 0 < k) :
    blockExponent r R N k .unrestricted ≤ arbitraryExponent r R N .unrestricted := by
  unfold blockExponent arbitraryExponent operational
  refine liminf_le_liminf (Eventually.of_forall fun eps => ?_)
  unfold blockRate arbitraryRate
  exact asym hk _ _ fun n q hq => num_le h hr hq eps

end arb

end X4H

end

-- ===== HSol

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

section
open X4H QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {a b : ℕ} (R : Set (Maps a b)) (N : Maps a b)
    (h : Setting R N) (k : ℕ) (hk : 0 < k) :
    (∀ c, blockExponent 1 R N k c ≤ blockExponent a R N k c) ∧
    (∀ r ∈ ({1, a} : Set ℕ),
      (blockExponent r R N 1 .unrestricted ≤ blockExponent r R N k .unrestricted ∧
       blockExponent r R N k .unrestricted ≤ arbitraryExponent r R N .unrestricted) ∧
      (∀ ell, 0 < ell → blockExponent r R N k .unrestricted ≤ blockExponent r R N (ell * k) .unrestricted) ∧
      blockExponent r R N k .product ≤ blockExponent r R N k .separable ∧
      blockExponent r R N k .separable ≤ blockExponent r R N k .unrestricted) := by
  refine ⟨fun c => exp_ref h.1 R N c, fun r hr => ?_⟩
  have hr0 : 0 < r := by
    rcases hr with rfl | hr
    · exact one_pos
    · rw [Set.mem_singleton_iff.mp hr]; exact h.1
  refine ⟨⟨?_, exp_arb h hr0 hk⟩, fun ell hell => exp_blk R N hell,
    op_mono fun m eps => rate_set R N adm_ps m eps,
    op_mono fun m eps => rate_set R N adm_su m eps⟩
  have := exp_blk (k := 1) (r := r) R N hk
  rwa [mul_one] at this

end

end
