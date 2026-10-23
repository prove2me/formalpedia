-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P38.lemma6_assistedCompression
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:34:06.874221+00:00
-- url     : https://prove2.me/submissions/641eb5b6-92fa-4d7f-bf3e-a4f7a1f0ec8d

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace X4L6

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

lemma phi_apply (p : X × X) : finiteMaxEntangled X p =
    if p.1 = p.2 then ((Real.sqrt (Fintype.card X))⁻¹ : ℂ) else 0 := rfl

lemma stepA (N : Superop X X) :
    effectProb (pureDensity (finiteMaxEntangled X))
      (idTensorSuperop (R := X) N (pureDensity (finiteMaxEntangled X))) =
    (∑ x : X, ∑ x' : X, ((Real.sqrt (Fintype.card X))⁻¹ : ℂ) * ((Real.sqrt (Fintype.card X))⁻¹ : ℂ) *
      N (Matrix.of fun i i' => if x = i' then if x' = i then
        ((Real.sqrt (Fintype.card X))⁻¹ : ℂ) * ((Real.sqrt (Fintype.card X))⁻¹ : ℂ) else 0 else 0) x' x).re := by
  unfold effectProb
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply, phi_apply,
    idTensorSuperop, Fintype.sum_prod_type]
  simp [ite_mul, mul_ite, apply_ite (starRingEnd ℂ), map_inv₀, Complex.conj_ofReal, Finset.sum_ite_eq]


variable {Y L Lp : Type} [Fintype Y] [Fintype L] [Fintype Lp]

/-- the amplitude `t_{jk}(x)` -/
def tt {m n : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ) (Dk : Fin n → Matrix X (Y × Lp) ℂ)
    (psi : EuclideanSpace ℂ (L × Lp)) (j : Fin m) (k : Fin n) (x : X) : ℂ :=
  ∑ a : Y × Lp, ∑ l : L, Dk k x a * Ek j a.1 (x, l) * psi (l, a.2)

lemma ac_apply (E : Superop (X × L) Y) (D : Superop (Y × Lp) X)
    (τ : Matrix (L × Lp) (L × Lp) ℂ) (ρ : Matrix X X ℂ) :
    assistedChannel E D τ ρ = D (Matrix.of fun a b => E (Matrix.of fun u v =>
      ρ u.1 v.1 * τ (u.2, a.2) (v.2, b.2)) a.1 b.1) := rfl

/-- `a_j(y,l') = Σ_l E_j y (x,l) ψ(l,l')` -/
def av {m : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ) (psi : EuclideanSpace ℂ (L × Lp)) (j : Fin m) (x : X) :
    Y × Lp → ℂ := fun a => ∑ l : L, Ek j a.1 (x, l) * psi (l, a.2)

lemma tt_eq {m n : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ) (Dk : Fin n → Matrix X (Y × Lp) ℂ)
    (psi : EuclideanSpace ℂ (L × Lp)) (j : Fin m) (k : Fin n) (x : X) :
    tt Ek Dk psi j k x = (Dk k *ᵥ av Ek psi j x) x := by
  simp only [tt, av, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma inner_eq {m : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ)
    (psi : EuclideanSpace ℂ (L × Lp)) (c : ℂ) (x x' : X) :
    (Matrix.of fun a b : Y × Lp => krausApply Ek (Matrix.of fun u v : X × L =>
      (Matrix.of fun i i' => if x = i' then if x' = i then c else 0 else 0) u.1 v.1 *
        pureDensity psi (u.2, a.2) (v.2, b.2)) a.1 b.1) =
    ∑ j, c • Matrix.vecMulVec (av Ek psi j x') (star (av Ek psi j x)) := by
  ext a b
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    pureDensity, Matrix.of_apply, Fintype.sum_prod_type, Matrix.smul_apply, Matrix.vecMulVec_apply,
    av, Pi.star_apply, star_sum, star_mul', smul_eq_mul]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l2 _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [RCLike.star_def]
  ring

lemma outer_eq {n : ℕ} {k : Fin n} (Dk : Fin n → Matrix X (Y × Lp) ℂ) (a b : Y × Lp → ℂ) (x x' : X) :
    (Dk k * Matrix.vecMulVec a (star b) * (Dk k)ᴴ) x' x = (Dk k *ᵥ a) x' * star ((Dk k *ᵥ b) x) := by
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
    dotProduct, Pi.star_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

lemma stepB {m n : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ) (Dk : Fin n → Matrix X (Y × Lp) ℂ)
    (psi : EuclideanSpace ℂ (L × Lp)) (c : ℂ) (x x' : X) :
    assistedChannel (krausApply Ek) (krausApply Dk) (pureDensity psi)
      (Matrix.of fun i i' => if x = i' then if x' = i then c else 0 else 0) x' x =
    c * ∑ j, ∑ k, tt Ek Dk psi j k x' * conj (tt Ek Dk psi j k x) := by
  rw [ac_apply, inner_eq]
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_apply, outer_eq, tt_eq, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl


section bounds

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]

lemma dot_star_self (w : κ → ℂ) : star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

/-- Kraus families are isometric. -/
lemma iso {n : ℕ} (K : Fin n → Matrix κ ι ℂ) (hK : IsKrausFamily K) (v : ι → ℂ) :
    ∑ k, ∑ i, ‖(K k *ᵥ v) i‖ ^ 2 = ∑ a, ‖v a‖ ^ 2 := by
  have h : ∀ k, star (K k *ᵥ v) ⬝ᵥ (K k *ᵥ v) = star v ⬝ᵥ (((K k)ᴴ * K k) *ᵥ v) := by
    intro k
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hsum : ∑ k, star (K k *ᵥ v) ⬝ᵥ (K k *ᵥ v) = star v ⬝ᵥ v := by
    simp only [h]
    rw [← dotProduct_sum, ← Matrix.sum_mulVec]
    unfold IsKrausFamily at hK
    rw [hK, Matrix.one_mulVec]
  simp only [dot_star_self] at hsum
  exact_mod_cast hsum

lemma cs (s : Finset ι) (f : ι → ℂ) : ‖∑ i ∈ s, f i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ s.card * ∑ i ∈ s, ‖f i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

end bounds


section main

variable {X Y L Lp : Type} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [Fintype L] [DecidableEq L] [Fintype Lp] [DecidableEq Lp]

lemma av_norm {m : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ) (hE : IsKrausFamily Ek)
    (psi : EuclideanSpace ℂ (L × Lp)) (hpsi : ∑ p, ‖psi p‖ ^ 2 = 1) (x : X) :
    ∑ j, ∑ a, ‖av Ek psi j x a‖ ^ 2 = 1 := by
  set f : Lp → X × L → ℂ := fun l' q => if q.1 = x then psi (q.2, l') else 0 with hf
  have hav : ∀ j a, av Ek psi j x a = (Ek j *ᵥ f a.2) a.1 := by
    intro j a
    simp only [av, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hf, mul_ite, mul_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  simp only [hav, Fintype.sum_prod_type]
  calc ∑ j, ∑ y, ∑ l', ‖(Ek j *ᵥ f l') y‖ ^ 2 = ∑ j, ∑ l', ∑ y, ‖(Ek j *ᵥ f l') y‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ l', ∑ j, ∑ y, ‖(Ek j *ᵥ f l') y‖ ^ 2 := Finset.sum_comm
    _ = ∑ l', ∑ q, ‖f l' q‖ ^ 2 := Finset.sum_congr rfl fun l' _ => iso Ek hE (f l')
    _ = 1 := by
        simp only [hf, Fintype.sum_prod_type, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero,
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_ite_irrel,
          Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.sum_comm, ← hpsi, Fintype.sum_prod_type]



lemma boundX {m n : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ) (hE : IsKrausFamily Ek)
    (Dk : Fin n → Matrix X (Y × Lp) ℂ) (hD : IsKrausFamily Dk)
    (psi : EuclideanSpace ℂ (L × Lp)) (hpsi : ∑ p, ‖psi p‖ ^ 2 = 1) :
    ∑ j, ∑ k, ‖∑ x, tt Ek Dk psi j k x‖ ^ 2 ≤ (Fintype.card X : ℝ) ^ 2 := by
  set d : ℝ := (Fintype.card X : ℝ)
  calc ∑ j, ∑ k, ‖∑ x, tt Ek Dk psi j k x‖ ^ 2
      ≤ ∑ j, ∑ k, d * ∑ x, ‖tt Ek Dk psi j k x‖ ^ 2 := by
        gcongr with j _ k _
        simpa [d] using cs Finset.univ (fun x => tt Ek Dk psi j k x)
    _ ≤ ∑ j, ∑ k, d * ∑ x, ∑ x'', ‖(Dk k *ᵥ av Ek psi j x) x''‖ ^ 2 := by
        gcongr with j _ k _ x _
        rw [tt_eq]
        exact Finset.single_le_sum (f := fun x'' => ‖(Dk k *ᵥ av Ek psi j x) x''‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ x)
    _ = d * ∑ j, ∑ x, ∑ k, ∑ x'', ‖(Dk k *ᵥ av Ek psi j x) x''‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = d * ∑ j, ∑ x, ∑ a, ‖av Ek psi j x a‖ ^ 2 := by
        simp only [iso Dk hD]
    _ = d * ∑ x, ∑ j, ∑ a, ‖av Ek psi j x a‖ ^ 2 := by rw [Finset.sum_comm]
    _ = d ^ 2 := by
        simp only [av_norm Ek hE psi hpsi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, d]
        ring


/-- `g_{k,y}(x,l) = Σ_{l'} D_k x (y,l') ψ(l,l')` -/
def gv {n : ℕ} (Dk : Fin n → Matrix X (Y × Lp) ℂ) (psi : EuclideanSpace ℂ (L × Lp)) (k : Fin n) (y : Y) :
    X × L → ℂ := fun q => ∑ l', Dk k q.1 (y, l') * psi (q.2, l')

lemma T_eq {m n : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ) (Dk : Fin n → Matrix X (Y × Lp) ℂ)
    (psi : EuclideanSpace ℂ (L × Lp)) (j : Fin m) (k : Fin n) :
    ∑ x, tt Ek Dk psi j k x = ∑ y, (Ek j *ᵥ gv Dk psi k y) y := by
  simp only [tt, gv, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring

lemma g_norm {n : ℕ} (Dk : Fin n → Matrix X (Y × Lp) ℂ) (hD : IsKrausFamily Dk)
    (psi : EuclideanSpace ℂ (L × Lp)) (hpsi : ∑ p, ‖psi p‖ ^ 2 = 1) (y : Y) :
    ∑ k, ∑ q, ‖gv Dk psi k y q‖ ^ 2 = 1 := by
  set h : L → Y × Lp → ℂ := fun l b => if b.1 = y then psi (l, b.2) else 0 with hh
  have hg : ∀ k q, gv Dk psi k y q = (Dk k *ᵥ h q.2) q.1 := by
    intro k q
    simp only [gv, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hh, mul_ite, mul_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  simp only [hg, Fintype.sum_prod_type]
  calc ∑ k, ∑ x, ∑ l, ‖(Dk k *ᵥ h l) x‖ ^ 2 = ∑ k, ∑ l, ∑ x, ‖(Dk k *ᵥ h l) x‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ x, ‖(Dk k *ᵥ h l) x‖ ^ 2 := Finset.sum_comm
    _ = ∑ l, ∑ b, ‖h l b‖ ^ 2 := Finset.sum_congr rfl fun l _ => iso Dk hD (h l)
    _ = 1 := by
        simp only [hh, Fintype.sum_prod_type, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero,
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_ite_irrel,
          Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [← hpsi, Fintype.sum_prod_type]

lemma boundY {m n : ℕ} (Ek : Fin m → Matrix Y (X × L) ℂ) (hE : IsKrausFamily Ek)
    (Dk : Fin n → Matrix X (Y × Lp) ℂ) (hD : IsKrausFamily Dk)
    (psi : EuclideanSpace ℂ (L × Lp)) (hpsi : ∑ p, ‖psi p‖ ^ 2 = 1) :
    ∑ j, ∑ k, ‖∑ x, tt Ek Dk psi j k x‖ ^ 2 ≤ (Fintype.card Y : ℝ) ^ 2 := by
  set e : ℝ := (Fintype.card Y : ℝ)
  simp only [T_eq]
  calc ∑ j, ∑ k, ‖∑ y, (Ek j *ᵥ gv Dk psi k y) y‖ ^ 2
      ≤ ∑ j, ∑ k, e * ∑ y, ‖(Ek j *ᵥ gv Dk psi k y) y‖ ^ 2 := by
        gcongr with j _ k _
        simpa [e] using cs Finset.univ (fun y => (Ek j *ᵥ gv Dk psi k y) y)
    _ ≤ ∑ j, ∑ k, e * ∑ y, ∑ y'', ‖(Ek j *ᵥ gv Dk psi k y) y''‖ ^ 2 := by
        gcongr with j _ k _ y _
        exact Finset.single_le_sum (f := fun y'' => ‖(Ek j *ᵥ gv Dk psi k y) y''‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ y)
    _ = e * ∑ k, ∑ y, ∑ j, ∑ y'', ‖(Ek j *ᵥ gv Dk psi k y) y''‖ ^ 2 := by
        simp only [← Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = e * ∑ k, ∑ y, ∑ q, ‖gv Dk psi k y q‖ ^ 2 := by
        simp only [iso Ek hE]
    _ = e * ∑ y, ∑ k, ∑ q, ‖gv Dk psi k y q‖ ^ 2 := by rw [Finset.sum_comm]
    _ = e ^ 2 := by
        simp only [g_norm Dk hD psi hpsi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, e]
        ring

end main

lemma ss : ((Real.sqrt (Fintype.card X))⁻¹ : ℂ) * ((Real.sqrt (Fintype.card X))⁻¹ : ℂ) =
    (((Fintype.card X : ℝ))⁻¹ : ℝ) := by
  have hd : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.le, Complex.ofReal_inv]

lemma reorder {m n : ℕ} (a : Fin m → Fin n → X → ℂ) (c : ℂ) :
    ∑ x, ∑ x', c * (c * ∑ j, ∑ k, a j k x' * conj (a j k x)) =
      c * c * ∑ j, ∑ k, ((‖∑ x, a j k x‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ j k, ((‖∑ x, a j k x‖ ^ 2 : ℝ) : ℂ) = ∑ x, ∑ x', a j k x' * conj (a j k x) := by
    intro j k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum,
      Finset.sum_comm]
  simp only [h1]
  have e1 : (∑ x, ∑ x', c * (c * ∑ j, ∑ k, a j k x' * conj (a j k x))) =
      c * c * ∑ x, ∑ x', ∑ j, ∑ k, a j k x' * conj (a j k x) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]
  congr 1
  calc ∑ x, ∑ x', ∑ j, ∑ k, a j k x' * conj (a j k x)
      = ∑ x, ∑ j, ∑ x', ∑ k, a j k x' * conj (a j k x) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ j, ∑ k, ∑ x', a j k x' * conj (a j k x) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ x, ∑ k, ∑ x', a j k x' * conj (a j k x) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ x, ∑ x', a j k x' * conj (a j k x) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm

end X4L6

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

theorem solution
    (X Y L Lprime : Type) [Fintype X] [Fintype Y] [Fintype L] [Fintype Lprime]
    [DecidableEq X] [DecidableEq Y] [DecidableEq L] [DecidableEq Lprime]
    [Nonempty X] [Nonempty Y] [Nonempty L] [Nonempty Lprime]
    (psi : EuclideanSpace ℂ (L × Lprime)) (hpsi : ‖psi‖ = 1)
    (E : Superop (X × L) Y) (hE : IsChannel E)
    (D : Superop (Y × Lprime) X) (hD : IsChannel D) :
    effectProb (pureDensity (finiteMaxEntangled X))
      (idTensorSuperop (R := X) (assistedChannel E D (pureDensity psi))
        (pureDensity (finiteMaxEntangled X))) ≤ (Fintype.card Y : ℝ) / Fintype.card X := by
  obtain ⟨m, Ek, hEK, hEeq⟩ := hE
  obtain ⟨n, Dk, hDK, hDeq⟩ := hD
  obtain rfl : E = krausApply Ek := funext hEeq
  obtain rfl : D = krausApply Dk := funext hDeq
  have hpsi2 : ∑ p, ‖psi p‖ ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq psi
    rw [hpsi] at this
    have h2 := congrArg (· ^ 2) this
    simp only [one_pow] at h2
    rw [h2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  rw [X4L6.stepA]
  simp only [X4L6.stepB]
  rw [X4L6.reorder (fun j k x => X4L6.tt Ek Dk psi j k x), X4L6.ss]
  set d : ℝ := (Fintype.card X : ℝ)
  set S : ℝ := ∑ j, ∑ k, ‖∑ x, X4L6.tt Ek Dk psi j k x‖ ^ 2 with hS
  have hre : ((d⁻¹ : ℝ) : ℂ) * ((d⁻¹ : ℝ) : ℂ) *
      ∑ j, ∑ k, ((‖∑ x, X4L6.tt Ek Dk psi j k x‖ ^ 2 : ℝ) : ℂ) = ((d⁻¹ * d⁻¹ * S : ℝ) : ℂ) := by
    push_cast [hS]; ring
  rw [hre, Complex.ofReal_re]
  have hd : 0 < d := by simp only [d]; exact_mod_cast Fintype.card_pos
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have h1 := X4L6.boundX Ek hEK Dk hDK psi hpsi2
  have h2 := X4L6.boundY Ek hEK Dk hDK psi hpsi2
  have hY : (0 : ℝ) ≤ Fintype.card Y := by positivity
  have hSle : S ≤ (Fintype.card Y : ℝ) * d := by
    rcases le_total (Fintype.card Y : ℝ) d with h | h
    · nlinarith
    · nlinarith
  rw [div_eq_mul_inv]
  calc d⁻¹ * d⁻¹ * S ≤ d⁻¹ * d⁻¹ * ((Fintype.card Y : ℝ) * d) := by gcongr
    _ = (Fintype.card Y : ℝ) * d⁻¹ := by field_simp
