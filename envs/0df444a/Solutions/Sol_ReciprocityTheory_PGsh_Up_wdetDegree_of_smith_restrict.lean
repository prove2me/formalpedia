-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.wdetDegree_of_smith_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:40.361716+00:00
-- url     : https://prove2.me/submissions/ec75dbdc-6f21-4a6a-9c98-647511bab931

import Definitions.Def_ReciprocityTheory_DualLattices_EigenQuotientSmithStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_SumValCoord
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_WdetDegreeOfSmithRestrict
import Theorems.Thm_ReciprocityTheory_PGsh_Up_idem_basis
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_det_le_one
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u4
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : EigenQuotientSmithStatement) (hR : RestrictedHopfOrderStatement) (hC : RestrictedHopfOrderApproximationStatement) :
    WdetDegStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw d X hd hX
  classical
  have hv := hSet.integers
  have hidem : e w * e w = e w := by rw [horth, if_pos rfl]
  have hρidem : H.ρ (e w) * H.ρ (e w) = H.ρ (e w) := by rw [← map_mul, hidem]
  obtain ⟨r, Bw, hrange, hker⟩ := idem_basis (H.ρ (e w)) hρidem
  obtain ⟨Λ, dj, hΛ, hdjspan, hdjv, hXeq⟩ :=
    hS p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange hker X hX
  obtain ⟨AW, hAWc, hOm⟩ := hR p g C v R O σ cp hSet H (e w) hidem r Bw hrange hker d hd
  have hcl := fun j => hC p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange
    hker (Λ j) (dj j) (hdjspan j) (hdjv j)
  choose x hxmem hxapp using hcl
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcp0 : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h1 := hSet.cp_val
    rw [h0, zero_pow (by omega)] at h1
    exact hSet.p_ne h1.symm
  have hdj0 : ∀ j, algebraMap R C (dj j) ≠ 0 := fun j h0 => by
    have h1 := hdjv j
    rw [h0, map_zero, le_zero_iff] at h1
    exact hcp0 h1
  have hpC : v (p : C) < 1 := by
    have h1 := hSet.p_lt
    rwa [map_natCast] at h1
  set u : Fin r → (Fin r → ZMod p) → C := fun j y => (algebraMap R C (dj j))⁻¹ * x j y with hudef
  have hred : ∀ y : Fin r → ZMod p, (fun i => PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p])) = y := by
    intro y
    funext i
    simp
  have hU2 : ∀ j y, v (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) < 1 := by
    intro j y
    have h1 := hxapp j (fun i => (((y i).val : ℕ) : ℤ_[p]))
    rw [hred y] at h1
    simp only [map_natCast] at h1
    have e1 : u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R)) =
        (x j y - algebraMap R C (dj j * ∑ i, Λ j i * ((y i).val : R))) / algebraMap R C (dj j) := by
      simp only [hudef, map_mul]
      field_simp [hdj0 j]
    rw [e1, map_div₀]
    exact (div_lt_one (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (hdj0 j)))).2 h1
  have hU1 : ∀ j y, v (u j y) ≤ 1 := by
    intro j y
    have e1 : u j y = (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) +
        algebraMap R C (∑ i, Λ j i * ((y i).val : R)) := by ring
    rw [e1]
    exact (Valuation.map_add v _ _).trans (max_le (hU2 j y).le (hv.map_le_one _))
  have h5 := (u5 p C v R hv hpC (Fin r) Λ u hΛ hU1 hU2).2 (fun j => algebraMap R C (dj j))
  have hxu : ∀ j y, algebraMap R C (dj j) * u j y = x j y := fun j y => by
    simp only [hudef]
    rw [mul_inv_cancel_left₀ (hdj0 j)]
  simp only [hxu] at h5
  have hxW : ∀ j, x j ∈ AW.carrier := fun j => hAWc ▸ hxmem j
  have hpow : ∀ (f : (Fin r → ZMod p) → C), f ∈ AW.carrier → ∀ k : ℕ, f ^ k ∈ AW.carrier := by
    intro f hf k
    induction k with
    | zero => rw [pow_zero]; exact AW.one_mem
    | succ k ih => rw [pow_succ]; exact AW.mul_mem _ _ ih hf
  have hmon : ∀ α : Fin r → ZMod p, (fun y => ∏ j, x j y ^ (α j).val) ∈ AW.carrier := by
    intro α
    have key : ∀ s : Finset (Fin r), (∏ j ∈ s, x j ^ (α j).val) ∈ AW.carrier := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.prod_empty]; exact AW.one_mem
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact AW.mul_mem _ _ (hpow _ (hxW a) _) ih
    convert key Finset.univ using 1
    funext y
    simp [Finset.prod_apply]
  obtain ⟨B, hBu, hBc⟩ := AW.lat
  have hcol : ∀ α : Fin r → ZMod p, ∃ c : (Fin r → ZMod p) → R,
      ∑ j', c j' • (fun y => B y j') = fun y => ∏ j, x j y ^ (α j).val := by
    intro α
    have h1 := hmon α
    rw [hBc] at h1
    exact (Submodule.mem_span_range_iff_exists_fun R).1 h1
  choose c hc using hcol
  have hMon : (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val) =
      B * Matrix.of fun j' α => algebraMap R C (c α j') := by
    ext y α
    have e := congrFun (hc α) y
    simp only [Finset.sum_apply, Pi.smul_apply] at e
    rw [Matrix.of_apply, ← e, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    simp only [Matrix.of_apply, Algebra.smul_def]
    ring
  have hvMon : v (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val).det ≤ v B.det := by
    rw [hMon, Matrix.det_mul, map_mul]
    calc v B.det * v (Matrix.of fun j' α => algebraMap R C (c α j')).det ≤ v B.det * 1 :=
          mul_le_mul' le_rfl (IsIntegralMat.det_le_one (v := v) fun j' α => hv.map_le_one _)
      _ = v B.det := mul_one _
  have hColen : HasColen R v AW.carrier (v B.det) := ⟨B, hBc, rfl⟩
  have hN : ∀ y : Fin r → ZMod p, p • y = 0 := by
    intro y
    funext i
    simp [nsmul_eq_mul, ZMod.natCast_self]
  have h4 := u4 p C v R hv hpC (Fin r → ZMod p) hN AW (v B.det) _ hColen hOm
  have hcard : Fintype.card (Fin r → ZMod p) = p ^ r := by simp
  rw [hcard] at h4
  set Y := ∏ j, v (algebraMap R C (dj j)) with hYdef
  set K := p ^ (Fintype.card (Fin r) - 1) * (p * (p - 1) / 2) with hKdef
  have hYK : Y ^ K ≤ v B.det := by
    rw [hYdef, ← Finset.prod_pow]
    exact h5 ▸ hvMon
  have hchain : Y ^ (2 * K) ≤ (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1)) := by
    calc Y ^ (2 * K) = (Y ^ K) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ≤ v B.det ^ 2 := by gcongr
      _ ≤ (v (algebraMap R C (p : R)) ^ d) ^ p ^ r := h4
      _ = (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1)) := by
        rw [← hSet.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
  rw [hXeq]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hY1 : Y = 1 := by simp [hYdef]
    rw [hY1] at hchain ⊢
    rw [one_pow] at hchain
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      simp
    · exfalso
      have hlt : (v (algebraMap R C cp) ^ d) ^ (p ^ 0 * (p - 1)) < 1 := by
        refine pow_lt_one₀ zero_le' (pow_lt_one₀ zero_le' ?_ (by omega)) (by simp; omega)
        have h1 := hSet.cp_val
        by_contra hge
        push_neg at hge
        have h2 : 1 ≤ v (algebraMap R C cp) ^ (p - 1) := one_le_pow₀ hge
        rw [h1] at h2
        exact absurd hSet.p_lt (not_lt.2 h2)
      exact absurd hchain (not_le.2 hlt)
  · have h2K : 2 * K = p ^ r * (p - 1) := by
      rw [hKdef, Fintype.card_fin, ← mul_assoc, mul_comm 2, mul_assoc,
        Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self p)]
      have : p ^ (r - 1) * p = p ^ r := by rw [← pow_succ]; congr 1; omega
      rw [← mul_assoc, this]
    rw [h2K] at hchain
    exact (pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))).1 hchain
end ReciprocityTheory.PGsh.Up
