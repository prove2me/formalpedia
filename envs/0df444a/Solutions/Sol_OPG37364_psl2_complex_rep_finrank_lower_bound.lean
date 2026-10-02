-- Prove2me | solution 1 for OPG37364.psl2_complex_rep_finrank_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T13:25:01.208261+00:00
-- url     : https://prove2.me/submissions/a1c709a2-2b85-4202-b3f4-dc2c08d6c8b9

/-
The representation-degree bound of DSV Theorem 3.5.1.
No graph-existence or spectral hypothesis is used in this file.
-/
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped MatrixGroups
open Matrix Matrix.SpecialLinearGroup Module

namespace OPG37364
namespace RepresentationBound

variable {q : ℕ} [Fact q.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Simplicity rules out every kernel except the identity subgroup. -/
theorem faithful_of_nontrivial (hq5 : 5 ≤ q)
    (ρ : Representation ℂ (PSL(2, ZMod q)) V) (hρ : ∃ g, ρ g ≠ 1) :
    Function.Injective ρ := by
  have : IsSimpleGroup PSL(2, ZMod q) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ q by omega))
  apply ρ.ker_eq_bot_iff.mp
  rcases Subgroup.Normal.eq_bot_or_eq_top (inferInstance : ρ.ker.Normal) with h | h
  · exact h
  · obtain ⟨g, hg⟩ := hρ
    have hr : ρ = 1 := MonoidHom.ker_eq_top_iff.mp h
    exact False.elim (hg (by simp [hr]))

/-- The canonical quotient, explicitly from SL₂ to PSL₂. -/
abbrev quotientMap : SL(2, ZMod q) →* PSL(2, ZMod q) :=
  QuotientGroup.mk' (Subgroup.center SL(2, ZMod q))

/-- Upper unipotents, as elements of PSL₂. -/
def unipotent (b : ZMod q) : PSL(2, ZMod q) :=
  quotientMap (transvection (show (0 : Fin 2) ≠ 1 by decide) b)

theorem unipotent_add (b c : ZMod q) :
    unipotent (b + c) = unipotent b * unipotent c := by
  simp only [unipotent, transvection_add, map_mul]

@[simp] theorem unipotent_zero : unipotent (0 : ZMod q) = 1 := by
  simp [unipotent, transvection_coeff_zero]

theorem unipotent_eq_one_iff (b : ZMod q) : unipotent b = 1 ↔ b = 0 := by
  change (QuotientGroup.mk _ : PSL(2, ZMod q)) = 1 ↔ b = 0
  rw [QuotientGroup.eq_one_iff, transvection_mem_center_iff]

theorem unipotent_one_pow (k : ℕ) :
    unipotent (1 : ZMod q) ^ k = unipotent (k : ZMod q) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, unipotent_add]

theorem unipotent_one_order : orderOf (unipotent (1 : ZMod q)) = q := by
  apply orderOf_eq_prime
  · simp [unipotent_one_pow]
  · exact (unipotent_eq_one_iff 1).not.mpr one_ne_zero

noncomputable def diagonal (a : ZMod q) (ha : a ≠ 0) : PSL(2, ZMod q) :=
  quotientMap (diag2 a ha)

/-- The SL identity is proved on matrices and then mapped to the PSL quotient. -/
theorem diagonal_conjugates (a : ZMod q) (ha : a ≠ 0) :
    diagonal a ha * unipotent (1 : ZMod q) * (diagonal a ha)⁻¹ =
      unipotent (a ^ 2) := by
  have hSL : diag2 a ha * transvection (show (0 : Fin 2) ≠ 1 by decide) 1 *
      (diag2 a ha)⁻¹ = transvection (show (0 : Fin 2) ≠ 1 by decide) (a ^ 2) := by
    rw [diag2_inv]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
        mul_inv_cancel₀ ha, inv_mul_cancel₀ ha, pow_two]
  simpa only [diagonal, unipotent, map_mul, map_inv] using congrArg quotientMap hSL

variable [FiniteDimensional ℂ V]

/-- Finite order is used via a separable annihilating polynomial, not merely via eigenvalue
existence. This rules out a nonidentity unipotent complex Jordan block. -/
theorem exists_nontrivial_eigenvalue (T : End ℂ V) (hpow : T ^ q = 1) (hne : T ≠ 1) :
    ∃ ζ : ℂ, T.HasEigenvalue ζ ∧ ζ ≠ 1 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hsemi : T.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (1 : ℂ) hq0 one_ne_zero).squarefree
      (by simpa using sub_eq_zero.mpr hpow)
  by_contra! h
  have htop : T.eigenspace 1 = ⊤ := by
    apply top_unique
    rw [← hsemi.iSup_eigenspace_eq_top]
    apply iSup_le
    intro ζ
    by_cases hz : T.HasEigenvalue ζ
    · rw [h ζ hz]
    · have hb : T.eigenspace ζ = ⊥ := not_not.mp hz
      simp [hb]
  apply hne
  ext v
  have hv : v ∈ T.eigenspace 1 := htop ▸ Submodule.mem_top
  simpa using Module.End.mem_eigenspace_iff.mp hv

omit [FiniteDimensional ℂ V] in
theorem primitive_eigenvalue (T : End ℂ V) (hpow : T ^ q = 1)
    {ζ : ℂ} (hζ : T.HasEigenvalue ζ) (hne : ζ ≠ 1) : IsPrimitiveRoot ζ q := by
  obtain ⟨v, hv⟩ := hζ.exists_hasEigenvector
  have hp : ζ ^ q = 1 := by
    apply smul_left_injective ℂ hv.2
    simpa [hpow] using (hv.pow_apply q).symm
  apply isPrimitiveRoot_of_mem_nthRootsFinset (Fact.out : q.Prime) _ hne
  exact (Polynomial.mem_nthRootsFinset (Fact.out : q.Prime).pos 1).mpr hp

omit [FiniteDimensional ℂ V] in
/-- Conjugation gives the square-exponent orbit of a nontrivial eigenvalue. -/
theorem square_eigenvalue (ρ : Representation ℂ (PSL(2, ZMod q)) V)
    {ζ : ℂ} (hζ : Module.End.HasEigenvalue (ρ (unipotent (1 : ZMod q))) ζ)
    (a : ZMod q) (ha : a ≠ 0) :
    Module.End.HasEigenvalue (ρ (unipotent (1 : ZMod q))) (ζ ^ (a ^ 2).val) := by
  obtain ⟨v, hv⟩ := hζ.exists_hasEigenvector
  let d := diagonal a ha
  have hc : unipotent (1 : ZMod q) * d⁻¹ =
      d⁻¹ * unipotent (1 : ZMod q) ^ (a ^ 2).val := by
    have hh := congrArg (fun x : PSL(2, ZMod q) => d⁻¹ * x) (diagonal_conjugates a ha)
    simpa [d, unipotent_one_pow, ZMod.natCast_zmod_val, mul_assoc] using hh
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := ρ d⁻¹ v)
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    calc
      ρ (unipotent 1) (ρ d⁻¹ v) = ρ (unipotent 1 * d⁻¹) v := by
        rw [map_mul, Module.End.mul_apply]
      _ = ρ (d⁻¹ * unipotent 1 ^ (a ^ 2).val) v := by rw [hc]
      _ = ρ d⁻¹ ((ρ (unipotent 1) ^ (a ^ 2).val) v) := by
        rw [map_mul, map_pow, Module.End.mul_apply]
      _ = ζ ^ (a ^ 2).val • ρ d⁻¹ v := by rw [hv.pow_apply, map_smul]
  · intro hz
    apply hv.2
    exact (ρ.apply_bijective d⁻¹).injective (by simpa using hz)

/-- Nonzero square residues; no character or spectral condition is hidden here. -/
def squareResidues : Finset (ZMod q) :=
  (Finset.univ.erase 0).image (fun a : ZMod q => a ^ 2)

/-- Each square has at most the two preimages `a` and `-a`. This cardinal inequality
is precisely enough for the division-free dimension bound. -/
theorem squareResidues_card_lower : q - 1 ≤ 2 * (squareResidues (q := q)).card := by
  classical
  let A : Finset (ZMod q) := Finset.univ.erase 0
  have hfib : ∀ b ∈ A.image (fun a => a ^ 2),
      (A.filter fun a => a ^ 2 = b).card ≤ 2 := by
    intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    apply (Finset.card_le_card (show (A.filter fun x => x ^ 2 = a ^ 2) ⊆ {a, -a} from ?_)).trans
      Finset.card_le_two
    intro x hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      sq_eq_sq_iff_eq_or_eq_neg.mp (Finset.mem_filter.mp hx).2
  calc
    q - 1 = A.card := by simp [A]
    _ = ∑ b ∈ A.image (fun a => a ^ 2), (A.filter fun a => a ^ 2 = b).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ _b ∈ A.image (fun a => a ^ 2), 2 := Finset.sum_le_sum hfib
    _ = 2 * (squareResidues (q := q)).card := by simp [squareResidues, A, Nat.mul_comm]

theorem squareResidues_card_le_finrank
    (ρ : Representation ℂ (PSL(2, ZMod q)) V) {ζ : ℂ}
    (hζ : Module.End.HasEigenvalue (ρ (unipotent (1 : ZMod q))) ζ)
    (hprim : IsPrimitiveRoot ζ q) :
    (squareResidues (q := q)).card ≤ Module.finrank ℂ V := by
  classical
  let S := squareResidues (q := q)
  have hev : ∀ x : S, Module.End.HasEigenvalue (ρ (unipotent (1 : ZMod q)))
      (ζ ^ (x : ZMod q).val) := by
    intro x
    obtain ⟨a, ha, hx⟩ := Finset.mem_image.mp x.property
    rw [← hx]
    exact square_eigenvalue ρ hζ a (Finset.mem_erase.mp ha).1
  have hinj : Function.Injective (fun x : S => ζ ^ (x : ZMod q).val) := by
    intro x y hxy
    apply Subtype.ext
    apply ZMod.val_injective q
    exact hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hxy
  choose v hv using fun x : S => (hev x).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent' (ρ (unipotent (1 : ZMod q)))
    (fun x : S => ζ ^ (x : ZMod q).val) hinj v hv
  simpa [S] using hli.fintype_card_le_finrank

end RepresentationBound
end OPG37364

open OPG37364

/-- DSV Theorem 3.5.1, for every nontrivial finite-dimensional complex representation.
Nontriviality refers to the action. Faithfulness and irreducibility are not hypotheses. -/
theorem solution
    (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (PSL(2, ZMod q)) V) (hρ : ∃ g, ρ g ≠ 1) :
    q - 1 ≤ 2 * Module.finrank ℂ V := by
  let : Fact q.Prime := ⟨hq⟩
  have hinj := RepresentationBound.faithful_of_nontrivial hq5 ρ hρ
  let u := RepresentationBound.unipotent (1 : ZMod q)
  let T : Module.End ℂ V := ρ u
  have hu : orderOf u = q := RepresentationBound.unipotent_one_order
  have hpow : T ^ q = 1 := by
    have hupow : u ^ q = 1 := by simpa only [hu] using pow_orderOf_eq_one u
    simpa only [map_pow, map_one] using congrArg ρ hupow
  have hne : T ≠ 1 := by
    intro hh
    have heq : u = 1 := hinj (hh.trans ρ.map_one.symm)
    have : (1 : ZMod q) = 0 := (RepresentationBound.unipotent_eq_one_iff 1).mp heq
    exact one_ne_zero this
  obtain ⟨ζ, hζ, hζ1⟩ := RepresentationBound.exists_nontrivial_eigenvalue T hpow hne
  have hprim := RepresentationBound.primitive_eigenvalue T hpow hζ hζ1
  exact RepresentationBound.squareResidues_card_lower.trans
    (Nat.mul_le_mul_left 2 (RepresentationBound.squareResidues_card_le_finrank ρ hζ hprim))
