-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:46:30.165498+00:00
-- url     : https://prove2.me/submissions/ca06dcb3-dc63-4e9d-83da-4dba11f53f1f

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_add_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_smul_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_sub_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_zero_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_sum_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_card_neg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_card_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r p : ℕ} (hp : p ≤ r) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsIntegralOn S L) (l v : Fin r → Fin r → K)
    (hl : ∀ j, l j ∈ L) (hvi : LinearIndependent K v)
    (hinj : ∀ g : ApproxPosIdx r p → K,
      (∀ k : ApproxPosIdx r p, S.h (l k.1) (∑ j : ApproxPosIdx r p, g j • l j.1) = 0) → g = 0) :
    ∃ (Δ : K) (coef : (Fin r → K) → ApproxPosIdx r p → K) (a : {j : Fin r // ¬ (j : ℕ) < p} → Fin r),
      Δ ≠ 0 ∧ Δ = (Matrix.of fun k j : ApproxPosIdx r p => S.h (l k.1) (l j.1)).det ∧
      (∀ x (k : ApproxPosIdx r p), S.h (l k.1) (Δ • x - ∑ k', coef x k' • l k'.1) = 0) ∧
      (∀ x ∈ L, Δ • x - ∑ k', coef x k' • l k'.1 ∈ L) ∧
      LinearIndependent K (fun j : Fin r => if h : (j : ℕ) < p then l j else
        Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l k'.1) := by
  classical
  set M : Matrix (ApproxPosIdx r p) (ApproxPosIdx r p) K := Matrix.of fun k j => S.h (l k.1) (l j.1) with hM
  set Δ := M.det with hΔdef
  let bv : (Fin r → K) → ApproxPosIdx r p → K := fun x k => S.h (l k.1) x
  let coef : (Fin r → K) → ApproxPosIdx r p → K := fun x => M.adjugate *ᵥ bv x
  let T : (Fin r → K) → (Fin r → K) := fun x => Δ • x - ∑ k', coef x k' • l k'.1

  have hMinj : ∀ g, M *ᵥ g = 0 → g = 0 := by
    intro g hg
    apply hinj g
    intro k
    have := congrFun hg k
    simp only [mulVec, dotProduct, hM, Matrix.of_apply, Pi.zero_apply] at this
    rw [approxB_h_sum_right]
    simpa [approxB_h_smul_right, mul_comm] using this
  have hΔ : Δ ≠ 0 := by
    intro h0
    obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hg0 (hMinj g hg)

  have horth : ∀ x (k : ApproxPosIdx r p), S.h (l k.1) (T x) = 0 := by
    intro x k
    have hMc : M *ᵥ coef x = Δ • bv x := by
      simp only [coef, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, hΔdef]
    have hk := congrFun hMc k
    simp only [mulVec, dotProduct, hM, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at hk
    simp only [T, approxB_h_sub_right, approxB_h_smul_right, approxB_h_sum_right]
    rw [← hk]
    simp [bv, mul_comm]

  have hint : ∀ x ∈ L, T x ∈ L := by
    intro x hx
    let f := algebraMap (𝓞 K) K
    have hMi : ∀ k j, ∃ z : 𝓞 K, f z = M k j := fun k j => hL _ (hl _) _ (hl _)
    choose Mz hMz using hMi
    have hbi : ∀ k, ∃ z : 𝓞 K, f z = bv x k := fun k => hL _ (hl _) _ hx
    choose bz hbz using hbi
    have hMmap : f.mapMatrix (Matrix.of Mz) = M := by ext k j; simp [hMz]
    have hΔz : f (Matrix.of Mz).det = Δ := by rw [RingHom.map_det, hMmap]
    have hcz : ∀ k, f (((Matrix.of Mz).adjugate *ᵥ bz) k) = coef x k := by
      intro k
      rw [show coef x = M.adjugate *ᵥ bv x from rfl, ← hMmap, ← RingHom.map_adjugate]
      simp only [mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum,
        map_mul, hbz]
    have hT : T x = (Matrix.of Mz).det • x -
        ∑ k', ((Matrix.of Mz).adjugate *ᵥ bz) k' • l k'.1 := by
      simp only [T, ← hΔz, ← hcz]
      simp only [f, algebraMap_smul]
    rw [hT]
    exact L.sub_mem (L.smul_mem _ hx) (L.sum_mem fun k _ => L.smul_mem _ (hl _))

  have hbadd : ∀ x y, bv (x + y) = bv x + bv y :=
    fun x y => funext fun k => approxB_h_add_right S _ x y
  have hbsmul : ∀ (c : K) x, bv (c • x) = c • bv x :=
    fun c x => funext fun k => by simp [bv, approxB_h_smul_right]
  let Tl : (Fin r → K) →ₗ[K] (Fin r → K) :=
    { toFun := T
      map_add' := fun x y => by
        simp only [T, coef, hbadd, mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
          smul_add]
        abel
      map_smul' := fun c x => by
        simp only [T, coef, hbsmul, mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          ← Finset.smul_sum, RingHom.id_apply, smul_sub]
        rw [smul_comm Δ c x] }
  have hker : LinearMap.ker Tl ≤ Submodule.span K (Set.range fun k : ApproxPosIdx r p => l k.1) := by
    intro x hx
    have h0 : T x = 0 := LinearMap.mem_ker.mp hx
    have hx' : x = Δ⁻¹ • ∑ k', coef x k' • l k'.1 := by
      have h1 : Δ • x = ∑ k', coef x k' • l k'.1 := sub_eq_zero.mp h0
      rw [← h1, smul_smul, inv_mul_cancel₀ hΔ, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfk : Module.finrank K (LinearMap.ker Tl) ≤ p := by
    calc _ ≤ Module.finrank K (Submodule.span K (Set.range fun k : ApproxPosIdx r p => l k.1)) :=
          Submodule.finrank_mono hker
      _ ≤ Fintype.card (ApproxPosIdx r p) := finrank_range_le_card (R := K) _
      _ = p := approxB_card_pos hp
  have hrn := LinearMap.finrank_range_add_finrank_ker Tl
  rw [Module.finrank_fin_fun] at hrn
  have hfr : r - p ≤ Module.finrank K (LinearMap.range Tl) := by omega
  have hspan_v : Submodule.span K (Set.range v) = ⊤ :=
    hvi.span_eq_top_of_card_eq_finrank' (by simp)
  have hrange : Submodule.span K (Set.range (Tl ∘ v)) = LinearMap.range Tl := by
    rw [Set.range_comp, ← Submodule.map_span, hspan_v, Submodule.map_top]
  obtain ⟨κ, a0, ha0, hsp, hli⟩ := exists_linearIndependent' K (Tl ∘ v)
  have : Finite κ := Finite.of_injective a0 ha0
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank K (LinearMap.range Tl) := by
    rw [← hrange, ← hsp, finrank_span_eq_card hli]
  have hle : Fintype.card {j : Fin r // ¬ (j : ℕ) < p} ≤ Fintype.card κ := by
    rw [approxB_card_neg hp, hcard]; exact hfr
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  have hlia : LinearIndependent K (fun k => T (v (a0 (e k)))) := hli.comp e e.injective
  refine ⟨Δ, coef, fun k => a0 (e k), hΔ, rfl, horth, hint, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsplit : ∑ k : ApproxPosIdx r p, g k.1 • l k.1 +
      ∑ k : {j : Fin r // ¬ (j : ℕ) < p}, g k.1 • T (v (a0 (e k))) = 0 := by
    rw [← hg, ← Fintype.sum_subtype_add_sum_subtype (fun j : Fin r => (j : ℕ) < p)]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by simp only [dif_pos k.2]
    · exact Finset.sum_congr rfl fun k _ => by simp only [dif_neg k.2]; rfl
  have hBorth : ∀ k' : ApproxPosIdx r p,
      S.h (l k'.1) (∑ k : {j : Fin r // ¬ (j : ℕ) < p}, g k.1 • T (v (a0 (e k)))) = 0 := by
    intro k'
    rw [approxB_h_sum_right]
    exact Finset.sum_eq_zero fun k _ => by rw [approxB_h_smul_right, horth, mul_zero]
  have hApos : ∀ k' : ApproxPosIdx r p, S.h (l k'.1) (∑ k : ApproxPosIdx r p, g k.1 • l k.1) = 0 := by
    intro k'
    have := congrArg (S.h (l k'.1)) hsplit
    rw [approxB_h_add_right, hBorth, add_zero, approxB_h_zero_right] at this
    exact this
  have hg1 := hinj (fun k => g k.1) hApos
  have hA0 : ∑ k : ApproxPosIdx r p, g k.1 • l k.1 = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [show g k.1 = 0 from congrFun hg1 k, zero_smul]
  rw [hA0, zero_add] at hsplit
  have hg2 := (Fintype.linearIndependent_iff.mp hlia) (fun k => g k.1) hsplit
  intro j
  by_cases hj : (j : ℕ) < p
  · exact congrFun hg1 ⟨j, hj⟩
  · exact hg2 ⟨j, hj⟩
end ReciprocityTheory.MultiplicativeHeights
