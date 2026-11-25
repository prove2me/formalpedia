-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.monomials_span_of_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:59:25.851575+00:00
-- url     : https://prove2.me/submissions/955cd09b-f676-4a62-be9e-4d8e6c463713

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_SumValCoord
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_MonomialsSpanOfProdEq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u4
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Basis
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
private lemma col_mem_span {X : Type} [Fintype X] (B' : Matrix X X C) (V : Matrix X X R) (j : X) :
    (fun x => (B' * V.map (algebraMap R C)) x j) ∈
      Submodule.span R (Set.range fun α x => B' x α) := by
  have e : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α) := by
    ext x
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
private lemma exists_factor {X : Type} [Fintype X] (B B' : Matrix X X C)
    (h : ∀ α, (fun x => B' x α) ∈ Submodule.span R (Set.range fun j x => B x j)) :
    ∃ W : Matrix X X R, B' = B * W.map (algebraMap R C) := by
  choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)
  refine ⟨Matrix.of fun j α => c α j, ?_⟩
  ext x α
  have h1 := congrFun (hc α) x
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at h1
  rw [Matrix.mul_apply, ← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]
private lemma prod_pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {ι : Type} [Fintype ι] (f : ι → N → C)
    (hf : ∀ j, f j ∈ A.carrier) (n : ι → ℕ) : (fun y => ∏ j, f j y ^ n j) ∈ A.carrier := by
  have hpow : ∀ j k, f j ^ k ∈ A.carrier := by
    intro j k
    induction k with
    | zero => simpa using A.one_mem
    | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih (hf j)
  have : (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j := by
    ext y; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb)
    A.one_mem (fun j _ => hpow j (n j))
private lemma hasLen_om {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) :
    HasLen v R (OmAA H.AA.carrier) (v (algebraMap R C (p : R)) ^ g) := by
  refine ⟨g, fun _ => (p : R), ⟨?_⟩, by simp⟩
  exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
    ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p g))
private lemma exp_eq (p g : ℕ) :
    g * (p ^ (g + g - 1) * (p * (p - 1) / 2)) * 2 = (p - 1) * g * p ^ (g + g) := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  have h2 : p * (p - 1) / 2 * 2 = p * (p - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have h3 : p ^ (g + g - 1) * p = p ^ (g + g) := by
    rw [← pow_succ]
    congr 1
    omega
  calc g * (p ^ (g + g - 1) * (p * (p - 1) / 2)) * 2 = g * p ^ (g + g - 1) * (p * (p - 1) / 2 * 2) := by ring
    _ = g * p ^ (g + g - 1) * (p * (p - 1)) := by rw [h2]
    _ = (p - 1) * g * (p ^ (g + g - 1) * p) := by ring
    _ = (p - 1) * g * p ^ (g + g) := by rw [h3]
end Basis
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : EigenLiftsBasisStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X hprod D
  classical
  have hv := hS.integers
  have hp1 : v (p : C) < 1 := by simpa [map_natCast] using hS.p_lt

  let B' : Matrix (Nb p g) (Nb p g) C := Matrix.of fun (x α : Nb p g) =>
    ∏ j, (algebraMap R C (D.ε j) * D.u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (D.ε j)) ^
      (p ^ (Fintype.card (Ix g) - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 (Ix g) D.Λ D.u D.Λ_det D.u_int D.u_cong).2 fun j => algebraMap R C (D.ε j)
  have hε : ∏ j, v (algebraMap R C (D.ε j)) = v (algebraMap R C cp) ^ g := by
    rw [← Finset.prod_fiberwise Finset.univ D.κ, ← hprod]
    exact Finset.prod_congr rfl fun i _ => D.ε_prod i
  have hcard : Fintype.card (Nb p g) = p ^ (g + g) := by
    simp [ZMod.card, Fintype.card_sum, Fintype.card_fin]
  have hsq : v B'.det ^ 2 = (v (algebraMap R C (p : R)) ^ g) ^ Fintype.card (Nb p g) := by
    rw [hB'v, Finset.prod_pow, hε, ← hS.cp_val, hcard]
    simp only [Fintype.card_sum, Fintype.card_fin, ← pow_mul]
    congr 1
    exact exp_eq p g

  obtain ⟨B, hBu, hAA⟩ := H.AA.lat
  have hcol : HasColen R v H.AA.carrier (v B.det) := ⟨B, hAA, rfl⟩
  have hN : ∀ x : Nb p g, p • x = 0 := by
    intro x; ext i; simp
  have hdeg := u4 p C v R hv hp1 (Nb p g) hN H.AA (v B.det) _ hcol (hasLen_om H)

  have hmem : ∀ α : Nb p g, (fun x => B' x α) ∈ H.AA.carrier := by
    intro α
    exact prod_pow_mem H.AA (fun j y => algebraMap R C (D.ε j) * D.u j y)
      (fun j => (Submodule.mem_inf.1 (D.x_mem j)).1) (fun j => (α j).val)
  obtain ⟨W, hW⟩ := exists_factor B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = v B.det * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det]; rfl
  have ha : v B.det ≠ 0 := (Valuation.ne_zero_iff v).2 hBu.ne_zero
  have hw1 : v (algebraMap R C W.det) ≤ 1 := hv.map_le_one W.det
  have hw : v (algebraMap R C W.det) = 1 := by
    by_contra hne
    have hlt : v (algebraMap R C W.det) < 1 := lt_of_le_of_ne hw1 hne
    have hpos : 0 < v B.det ^ 2 := pow_pos (pos_iff_ne_zero.2 ha) 2
    have : v B'.det ^ 2 < v B.det ^ 2 := by
      rw [hdet, mul_pow]
      exact mul_lt_of_lt_one_right hpos (pow_lt_one₀ zero_le hlt two_ne_zero)
    rw [hsq] at this
    exact absurd hdeg (not_le.2 this)
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have hspan : Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan]
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := col_mem_span B' (W⁻¹) j
    rwa [hBeq] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α
end ReciprocityTheory.PGsh.Up
