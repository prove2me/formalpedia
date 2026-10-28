-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.twoParty_specialization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:48:07.553604+00:00
-- url     : https://prove2.me/submissions/530802e7-a97b-4d5c-afc1-5e51b537506b

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_pure_tripartite_entropy_balances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped Matrix ComplexOrder ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X9TwoParty

private def reindexStar {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; exact Matrix.conjTranspose_reindex e e A
    map_smul' := by intros; rfl }

private lemma entropy_reindex {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) :
    vnEntropy (Matrix.reindex e e A) = vnEntropy A := by
  let f : ℝ → ℝ := fun x => x * Real.logb 2 x
  let phi := reindexStar e
  have ht (B : Matrix I I ℂ) : (phi B).trace = B.trace :=
    Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  have hc : cfc f (phi A) = phi (cfc f A) := by
    by_cases hA : A.IsHermitian
    · have hphiA : (phi A).IsHermitian := hA.submatrix e.symm
      have hf : Continuous f := by
        simpa [f, Real.logb, mul_div_assoc] using
          Real.continuous_mul_log.div_const (Real.log 2)
      exact (StarAlgHomClass.map_cfc (S := ℂ) phi f A hf.continuousOn
        (by change Continuous (fun B : Matrix I I ℂ => B.submatrix e.symm e.symm); fun_prop)
        hA hphiA).symm
    · have hphiA : ¬ (phi A).IsHermitian := by
        intro h
        apply hA
        have hh := h.submatrix e
        convert hh using 1 <;> ext i j <;> simp [phi, reindexStar, Matrix.submatrix]
      have hz : cfc f A = 0 := cfc_apply_of_not_predicate A hA
      have hz' : cfc f (phi A) = 0 := cfc_apply_of_not_predicate (phi A) hphiA
      exact hz'.trans ((map_zero phi).symm.trans (congrArg phi hz.symm))
  change -(cfc f (phi A)).trace.re = -(cfc f A).trace.re
  rw [hc, ht]

private def emptyEquiv {m : ℕ} (D : Fin m → Type) (R : Type) :
    SubBasis D ∅ × R ≃ R where
  toFun a := a.2
  invFun r := (fun i => False.elim (Finset.notMem_empty i.val i.property), r)
  left_inv a := by
    apply Prod.ext
    · funext i; exact False.elim (Finset.notMem_empty i.val i.property)
    · rfl
  right_inv _ := rfl

private lemma entropyAt_empty {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    entropyAt rho ∅ = vnEntropy (traceLeft rho) := by
  have he : Matrix.reindex (emptyEquiv D R) (emptyEquiv D R)
      (registerMarginal rho ∅) = traceLeft rho := by
    ext a b
    change registerMarginal rho ∅ ((emptyEquiv D R).symm a)
      ((emptyEquiv D R).symm b) = traceLeft rho a b
    simp only [registerMarginal, Finset.notMem_empty, IsEmpty.forall_iff,
      not_false_eq_true, true_implies, implies_true, forall_true_iff, true_and]
    have h (x y : RegisterBasis D) : (∀ i, x i = y i) ↔ y = x :=
      ⟨fun h => (funext h).symm, fun h => by subst y; simp⟩
    change (∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
      if (∀ i, x i = y i) then rho (x,a) (y,b) else 0) = _
    simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  unfold entropyAt
  convert (entropy_reindex (emptyEquiv D R) (registerMarginal rho ∅)).symm.trans
    (congrArg vnEntropy he) using 1

private lemma threshold_empty {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    entropyThreshold rho ∅ = 0 := by
  simp [entropyThreshold, entropyAt_empty]



private def allEquiv {m : ℕ} (D : Fin m → Type) (R : Type) :
    SubBasis D Finset.univ × R ≃ RegisterBasis D × R where
  toFun a := (fun i => a.1 ⟨i,Finset.mem_univ i⟩, a.2)
  invFun a := (fun i => a.1 i.val, a.2)
  left_inv a := by
    apply Prod.ext
    · funext i; rfl
    · rfl
  right_inv a := by
    apply Prod.ext
    · funext i; rfl
    · rfl

private lemma marginal_univ {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type}
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    Matrix.reindex (allEquiv D R) (allEquiv D R) (registerMarginal rho Finset.univ) = rho := by
  ext a b
  change registerMarginal rho Finset.univ ((allEquiv D R).symm a)
    ((allEquiv D R).symm b) = rho a b
  have h (x y : RegisterBasis D) :
      (∀ i, x i = a.1 i ∧ y i = b.1 i) ↔ x = a.1 ∧ y = b.1 := by
    constructor
    · intro h; exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩
    · rintro ⟨rfl,rfl⟩; simp
  simp only [registerMarginal, Finset.mem_univ, not_true_eq_false, false_implies,
    forall_const, and_true, allEquiv, Equiv.coe_fn_symm_mk, true_implies]
  simp only [h, ite_and]
  simp

private lemma entropyAt_univ {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    entropyAt rho Finset.univ = vnEntropy rho := by
  unfold entropyAt
  convert (entropy_reindex (allEquiv D R) (registerMarginal rho Finset.univ)).symm.trans
    (congrArg vnEntropy (marginal_univ rho)) using 1

private lemma pure_entropy {I : Type} [Fintype I] [DecidableEq I]
    (psi : EuclideanSpace ℂ I) (hpsi : ‖psi‖ = 1) :
    vnEntropy (pureDensity psi) = 0 := by
  have hn : (∑ i, conj (psi i) * psi i) = (1 : ℂ) := by
    calc
      _ = inner ℂ psi psi := by simp only [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      _ = 1 := by rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hid : IsIdempotentElem (pureDensity psi) := by
    change pureDensity psi * pureDensity psi = pureDensity psi
    ext i j
    simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply]
    calc
      _ = psi i * (∑ k, conj (psi k) * psi k) * conj (psi j) := by
        simp only [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl
        intro k hk; ring
      _ = _ := by rw [hn]; ring
  have hs := hid.spectrum_subset ℝ
  have hc : cfc (fun x : ℝ => x * Real.logb 2 x) (pureDensity psi) = 0 := by
    calc
      _ = cfc (fun _ : ℝ => 0) (pureDensity psi) := by
        apply cfc_congr
        intro x hx
        have hm := hs hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with rfl | rfl <;> simp
      _ = 0 := by simp
  simp [vnEntropy, hc]

private lemma pure_complement {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) :
    vnEntropy (traceRight (pureDensity psi)) = vnEntropy (traceLeft (pureDensity psi)) := by
  let e : A × B ≃ (A × Unit) × B :=
    (Equiv.prodCongr (Equiv.prodUnique A Unit).symm (Equiv.refl B))
  let v := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e psi
  have hv : IsState v := (LinearIsometryEquiv.norm_map _ psi).trans hpsi
  have h := (QAlgorithms.Papers.Independent.Renew46.P34.pure_tripartite_entropy_balances v hv).1
  have hab : QAlgorithms.Papers.Independent.Renew46.P34.sourceAB v =
      Matrix.reindex (Equiv.prodUnique A Unit).symm (Equiv.prodUnique A Unit).symm
        (traceRight (pureDensity psi)) := by
    ext i j; rfl
  have hb : traceLeft (pureDensity v) = traceLeft (pureDensity psi) := by
    ext i j
    simp [traceLeft, pureDensity, v, e, Equiv.prodUnique, Equiv.prodPUnit,
      LinearIsometryEquiv.piLpCongrLeft, Matrix.vecMulVec, Fintype.sum_prod_type]
  calc
    vnEntropy (traceRight (pureDensity psi)) =
        vnEntropy (Matrix.reindex (Equiv.prodUnique A Unit).symm
          (Equiv.prodUnique A Unit).symm (traceRight (pureDensity psi))) := by
      convert (entropy_reindex (Equiv.prodUnique A Unit).symm
        (traceRight (pureDensity psi))).symm using 1
    _ = vnEntropy (QAlgorithms.Papers.Independent.Renew46.P34.sourceAB v) := by
      exact congrArg vnEntropy hab.symm
    _ = vnEntropy (traceLeft (pureDensity v)) := by convert h using 1 <;> congr 1
    _ = vnEntropy (traceLeft (pureDensity psi)) := by exact congrArg vnEntropy hb

private lemma one_info {D : Fin 1 → Type} [∀ i, Fintype (D i)]
    {E : Type} [Fintype E]
    (sigma : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) :
    conditionalMultipartiteInformation .total sigma (singleParties 1) ∅ = 0 := by
  simp [conditionalMultipartiteInformation, singleParties, allParties]

private lemma one_squashed {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hm : m = 1) :
    halfExtensionSquashed .total rho = 0 := by
  subst m
  let S : Set ℝ := {v : ℝ | ∃ e : ℕ, 0 < e ∧
    ∃ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
      IsDensityMatrix sigma ∧ forgetEnvironment sigma = rho ∧
      (false = true → IsClassicalExtension sigma) ∧
      v = conditionalMultipartiteInformation .total sigma (singleParties 1) ∅}
  have hz {v : ℝ} (hv : v ∈ S) : v = 0 := by
    obtain ⟨e,he,sigma,hden,hred,hclass,hval⟩ := hv
    exact hval.trans (one_info sigma)
  have hi : sInf S = 0 := by
    by_cases h : S.Nonempty
    · have he : S = {0} := Set.Subset.antisymm
        (fun _ hv => by simpa using hz hv)
        (Set.singleton_subset_iff.mpr (by
          obtain ⟨v,hv⟩ := h
          simpa only [hz hv] using hv))
      rw [he]; exact csInf_singleton 0
    · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]
  change sInf S / 2 = 0
  rw [hi]; norm_num

private lemma squashed_singleton {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) (i : Fin m) :
    subsetSquashed rho {i} = 0 := by
  rw [subsetSquashed, if_neg (Finset.singleton_ne_empty i)]
  exact one_squashed _ (Finset.card_singleton i)

private def canonical : Fin 2 ≃o (Finset.univ : Finset (Fin 2)) where
  toFun i := ⟨i, Finset.mem_univ i⟩
  invFun i := i.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
private lemma canonical_eq :
    (Finset.univ : Finset (Fin 2)).orderIsoOfFin rfl = canonical := by
  let o : Fin 2 ≃o (Finset.univ : Finset (Fin 2)) := Finset.univ.orderIsoOfFin rfl
  have hmono : StrictMono (fun j : Fin 2 => (o j).val) := by
    intro i j hij
    exact o.strictMono hij
  have he (i : Fin 2) : (o i).val = i := congrFun hmono.eq_id i
  ext i
  exact congrArg Fin.val (he i)

private def fullSelected {D : Fin 2 → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (o : Fin 2 ≃o (Finset.univ : Finset (Fin 2))) :
    Matrix (RegisterBasis (fun i => D (o i).val))
      (RegisterBasis (fun i => D (o i).val)) ℂ :=
  fun a b => forgetEnvironment (registerMarginal rho Finset.univ)
    (fun i => cast (congrArg (fun j : (Finset.univ : Finset (Fin 2)) => D j.val)
      (o.apply_symm_apply i)) (a (o.symm i)))
    (fun i => cast (congrArg (fun j : (Finset.univ : Finset (Fin 2)) => D j.val)
      (o.apply_symm_apply i)) (b (o.symm i)))

private lemma squashed_univ {D : Fin 2 → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    subsetSquashed rho Finset.univ = halfExtensionSquashed .total (forgetEnvironment rho) := by
  rw [subsetSquashed, if_neg (show (Finset.univ : Finset (Fin 2)) ≠ ∅ from
    Finset.univ_nonempty.ne_empty)]
  change halfExtensionSquashed .total
    (fullSelected rho ((Finset.univ : Finset (Fin 2)).orderIsoOfFin rfl)) = _
  rw [canonical_eq]
  congr 1
  ext a b
  change (∑ r, registerMarginal rho Finset.univ
    ((fun i => a i.val),r) ((fun i => b i.val),r)) = ∑ r, rho (a,r) (b,r)
  apply Finset.sum_congr rfl
  intro r hr
  exact congrFun (congrFun (marginal_univ rho) (a,r)) (b,r)

private lemma four_subsets (K : Finset (Fin 2)) :
    K = ∅ ∨ K = {0} ∨ K = {1} ∨ K = Finset.univ := by
  by_cases h0 : 0 ∈ K <;> by_cases h1 : 1 ∈ K
  · right; right; right
    ext i; fin_cases i <;> simp_all
  · right; left
    ext i; fin_cases i <;> simp_all
  · right; right; left
    ext i; fin_cases i <;> simp_all
  · left
    ext i; fin_cases i <;> simp_all

private lemma four_constraints (f : Finset (Fin 2) → ℝ) (Q : Fin 2 → ℝ)
    (h0 : f ∅ = 0) :
    (∀ K, f K ≤ ∑ i ∈ K, Q i) ↔
      f {0} ≤ Q 0 ∧ f {1} ≤ Q 1 ∧ f Finset.univ ≤ Q 0 + Q 1 := by
  constructor
  · intro h
    exact ⟨by simpa using h {0}, by simpa using h {1},
      by simpa only [Fin.sum_univ_two] using h Finset.univ⟩
  · rintro ⟨h1,h2,ht⟩ K
    rcases four_subsets K with rfl | rfl | rfl | rfl
    · simp [h0]
    · simpa using h1
    · simpa using h2
    · simpa only [Fin.sum_univ_two] using ht

private lemma threshold_univ {D : Fin 2 → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {R : Type} [Fintype R] [Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1) :
    entropyThreshold (pureDensity phi) Finset.univ =
      (entropyAt (trivialExtension (forgetEnvironment (pureDensity phi))) {0} +
        entropyAt (trivialExtension (forgetEnvironment (pureDensity phi))) {1} +
        vnEntropy (forgetEnvironment (pureDensity phi))) / 2 := by
  have he : vnEntropy (traceLeft (pureDensity phi)) =
      vnEntropy (forgetEnvironment (pureDensity phi)) := by
    convert (pure_complement phi hphi).symm using 1 <;> congr 1
  simp [entropyThreshold, entropyAt_univ, pure_entropy phi hphi,
    Fin.sum_univ_two, he]

end X9TwoParty


open X9TwoParty

theorem solution {D : Fin 2 → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {R : Type} [Fintype R] [Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1) (Q : Fin 2 → ℝ) :
    let rho := pureDensity phi
    let a := forgetEnvironment rho
    let H1 := entropyAt (trivialExtension a) {0}
    let H2 := entropyAt (trivialExtension a) {1}
    let I1 := H1 + vnEntropy (traceLeft rho) - entropyAt rho {0}
    let I2 := H2 + vnEntropy (traceLeft rho) - entropyAt rho {1}
    (Q ∈ entropyPolyhedron rho ↔ I1/2 ≤ Q 0 ∧ I2/2 ≤ Q 1 ∧
      (H1 + H2 + vnEntropy a)/2 ≤ Q 0 + Q 1) ∧
    (Q ∈ outerPolyhedron rho ↔ I1/2 ≤ Q 0 ∧ I2/2 ≤ Q 1 ∧
      (H1 + H2 + vnEntropy a)/2 - halfExtensionSquashed .total a ≤ Q 0 + Q 1)  := by
  dsimp only
  have ht := threshold_univ phi hphi
  constructor
  · change (∀ K, entropyThreshold (pureDensity phi) K ≤ ∑ i ∈ K, Q i) ↔ _
    rw [four_constraints _ Q (threshold_empty _)]
    rw [ht]
    simp only [entropyThreshold, Finset.sum_singleton]
  · change (∀ K, entropyThreshold (pureDensity phi) K - subsetSquashed (pureDensity phi) K ≤
      ∑ i ∈ K, Q i) ↔ _
    have h0 : entropyThreshold (pureDensity phi) ∅ - subsetSquashed (pureDensity phi) ∅ = 0 := by
      simp [threshold_empty, subsetSquashed]
    rw [four_constraints _ Q h0]
    rw [squashed_singleton, squashed_singleton, squashed_univ, ht]
    simp only [sub_zero, entropyThreshold, Finset.sum_singleton]

