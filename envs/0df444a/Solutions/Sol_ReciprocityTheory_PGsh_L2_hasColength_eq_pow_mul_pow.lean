-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.hasColength_eq_pow_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:27:14.846572+00:00
-- url     : https://prove2.me/submissions/760b12e9-2f7d-4269-a9e4-533b27485d4e

import Definitions.Def_ReciprocityTheory_DualLattices_MemSupOfRestrictToSubgroupMemSq
import Definitions.Def_ReciprocityTheory_DualLattices_HasColengthEqPowMulPow
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_expand
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_mem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_pullbackQuotient_mul
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_sum
import Theorems.Thm_ReciprocityTheory_PGsh_L2_det_map_algebraMap
import Theorems.Thm_ReciprocityTheory_PGsh_L2_eq_one_of_le_one_of_mul_eq_one
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_basis_map_restrictToSubgroup
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_coset_basis
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_family_valuation_det_eq_one
import Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_eq_of_span_eq_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
private theorem valuation_det_le_one_of_integral_entries (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (E : Matrix X X C) (hE : ∀ i j, ∃ r : R, algebraMap R C r = E i j) : v E.det ≤ 1 := by
  choose M hM using hE
  have hEM : E = (Matrix.of M).map (algebraMap R C) := by
    ext i j
    exact (hM i j).symm
  rw [hEM, det_map_algebraMap]
  exact hv.map_le_one _
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)] :
    ∀ c cB cK, HasColen R v AA.carrier c →
      HasColen R v (AA.carrier.comap (pullQ (R := R) K)) cB →
      HasColen R v (AA.carrier.map (resK (R := R) K)) cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  intro c cB cK hc hcB hcK
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hfA, hfu⟩ := exists_coset_basis hv AA K
  obtain ⟨g, hgA, hgdet⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨P, hP, rfl⟩ := hc
  obtain ⟨Q, hQ, rfl⟩ := hcB
  obtain ⟨β', hβ', rfl⟩ := hcK
  obtain ⟨P0, hP0, hAP0⟩ := AA.lat
  have hint : ∀ {F : N → C}, F ∈ AA.carrier → ∀ x, ∃ r : R, algebraMap R C r = F x :=
    fun hF x => AA.le_int hF x
  have hK : v β'.det = v β.det := valuation_det_eq_of_span_eq_alt hv hβ (hAK.symm.trans hβ')
  have hmm1 : ∀ x, v (h3mm K β f x).det = 1 := by
    intro x
    have hdec : ∀ l, ∃ e : K → N ⧸ K → C,
        (∀ j, e j ∈ AA.carrier.comap (pullQ (R := R) K)) ∧
          g l = ∑ j, pullQ (R := R) K (e j) * f j := by
      intro l
      obtain ⟨b, ⟨hb, hgb⟩, -⟩ := hfu (g l) (hgA l)
      choose e he hbe using fun j => Submodule.mem_map.mp (hb j)
      refine ⟨e, he, ?_⟩
      rw [hgb]
      exact Finset.sum_congr rfl fun j _ => by rw [hbe j]
    choose e he hge using hdec
    let Bx : Matrix K K C := Matrix.of fun l j => e l j (x : N ⧸ K)
    have hmul : h3mm K β g x = Bx * h3mm K β f x := by
      ext l m
      simp only [h3mm, Matrix.of_apply, Matrix.mul_apply, Bx]
      rw [hge l, cosetCoordinates_sum, Finset.sum_apply]
      simp only [cosetCoordinates_pullbackQuotient_mul, Pi.smul_apply, smul_eq_mul]
    have hB1 : v Bx.det ≤ 1 := valuation_det_le_one_of_integral_entries hv Bx fun l j => by
      obtain ⟨r, hr⟩ := hint (Submodule.mem_comap.mp (he l j)) x
      exact ⟨r, hr⟩
    have hF1 : v (h3mm K β f x).det ≤ 1 := valuation_det_le_one_of_integral_entries hv _ fun j m =>
      hint (cosetCoordinates_mem AA K β hβ hAK (hfA j) m) x
    have h := hgdet x
    rw [hmul, Matrix.det_mul, map_mul, mul_comm] at h
    exact eq_one_of_le_one_of_mul_eq_one hF1 hB1 h
  let e : K × (N ⧸ K) ≃ N := (Equiv.prodComm _ _).trans (quotientProdSubgroupEquiv K)
  have he_apply : ∀ p : K × (N ⧸ K), e p = p.2.out + p.1 := fun p => rfl
  let Φ : Matrix N N C := fun x n => Q (x : N ⧸ K) (e.symm n).2 * f (e.symm n).1 x
  have hspan : AA.carrier = Submodule.span R (Set.range fun n x => Φ x n) := by
    apply le_antisymm
    · intro G hG
      obtain ⟨b, ⟨hb, hGb⟩, -⟩ := hfu G hG
      rw [hGb]
      refine sum_mem fun j _ => ?_
      obtain ⟨b', hb', hbb'⟩ := Submodule.mem_map.mp (hb j)
      rw [hQ] at hb'
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hb'
      rw [← hbb', ← hr, map_sum, Finset.sum_mul]
      refine sum_mem fun s _ => ?_
      rw [map_smul, smul_mul_assoc]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e (j, s), ?_⟩)
      funext x
      simp only [Φ, Equiv.symm_apply_apply]
      rfl
    · rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      have h1 : (fun q : N ⧸ K => Q q (e.symm n).2) ∈ AA.carrier.comap (pullQ (R := R) K) := by
        rw [hQ]
        exact Submodule.subset_span ⟨_, rfl⟩
      exact AA.mul_mem _ _ h1 (hfA _)
  have hdetΦ : v Φ.det = v Q.det ^ Fintype.card K * v β.det ^ Fintype.card (N ⧸ K) := by
    rw [← Matrix.det_submatrix_equiv_self e Φ]
    have hblk : Φ.submatrix e e = Matrix.blockDiagonal (fun q : N ⧸ K =>
        β * (h3mm K β f q.out)ᵀ) * Matrix.kroneckerMap (· * ·) (1 : Matrix K K C) Q := by
      ext ⟨k, q⟩ ⟨j, s⟩
      show Q ((e (k, q) : N) : N ⧸ K) (e.symm (e (j, s))).2 * f (e.symm (e (j, s))).1 (e (k, q)) = _
      rw [Equiv.symm_apply_apply, he_apply]
      dsimp only
      rw [quotient_out_add_coe K q k, cosetCoordinates_expand K β hβ (f j) q.out k, Matrix.mul_apply]
      simp only [Fintype.sum_prod_type, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_one, mul_zero, one_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
      conv_rhs => rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp only [eq_self_iff_true, if_true, Finset.sum_ite_eq, Finset.mem_univ]
      rw [mul_comm]
      rfl
    have hq : ∀ q : N ⧸ K, v (β * (h3mm K β f q.out)ᵀ).det = v β.det := by
      intro q
      rw [Matrix.det_mul, Matrix.det_transpose, map_mul, hmm1, mul_one]
    rw [hblk, Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_kronecker, Matrix.det_one,
      one_pow, one_mul, map_mul, map_prod, map_pow]
    simp only [hq, Finset.prod_const, Finset.card_univ]
    ring
  have h1 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hP)
  have h2 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hspan)
  rw [h1, ← h2, hdetΦ, hK]
end ReciprocityTheory.PGsh.L2
