-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.transFin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:08.530306+00:00
-- url     : https://prove2.me/submissions/bc1c3822-348e-4064-82cc-13976ee0be36

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFin
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_rc_comm
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_lift_alg
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_coef
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_common_ker
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_eig_prod
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_fin_adjoin
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_inv_of_alg
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_left_inv_prod
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_qdet_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → JMComm → StepFormula → QdetFacts → Spectrum → Chain → ColAnti → TransFin := by
  intro hT hJ hS hQ hSp hC hCA
  intro n M _ _ E hE l hl ℓ hℓ hW hn m col b co hmono htab hcol
  let top : Fin n := ⟨n - 1, by omega⟩
  have htop : (top : ℕ) + 1 = n := by
    show n - 1 + 1 = n
    omega
  have hE' : GlRel (tE (Finset.univ : Finset (Fin m)) E) := (hT n M (Fin m) E hE Finset.univ).1
  obtain ⟨c, hc⟩ := (hQ n (TV n M (Fin m)) (tE (Finset.univ : Finset (Fin m)) E) hE').2.1
  set B : Subalgebra ℂ (Module.End ℂ (TV n M (Fin m))) :=
    Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j) with hB
  set A := envAlg fun _ : Unit => tE (Finset.univ : Finset (Fin m)) E with hA
  have hxcomm : ∀ i j : Fin m, Commute (xJ E i) (xJ E j) := (hJ n M E hE m).1
  have hxB : ∀ j, xJ E j ∈ B := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y := by
    intro x hx y hy
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy ?_
    rintro _ ⟨j, rfl⟩
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_).symm
    rintro _ ⟨i, rfl⟩
    exact hxcomm j i
  have hcs : ∀ (f : TV n M (Fin m) →ₗ[ℂ] ℂ) (h : ℕ → Module.End ℂ (TV n M (Fin m))),
      f ∘ₗ (∑ i ∈ Finset.range (n + 1), h i) = ∑ i ∈ Finset.range (n + 1), f ∘ₗ h i := by
    intro f h
    refine LinearMap.ext fun v => ?_
    simp
  set N : ℤ := ∑ k, |l k| with hN
  have hlN : ∀ k, 0 ≤ l k + N := by
    intro k
    have h1 : |l k| ≤ N :=
      Finset.single_le_sum (f := fun k => |l k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 := neg_abs_le (l k)
    linarith
  have hsp := hSp n M E hE (fun k => (l k : ℂ)) (-(N : ℂ)) hl (fun k => ⟨(l k + N).toNat, by
      rw [show (((l k + N).toNat : ℕ) : ℂ) = ((l k + N : ℤ) : ℂ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (hlN k)]]
      push_cast
      ring⟩) m
  choose L hL using hsp.2
  let L' : Fin m → List ℂ := fun j => (L j).map (fun r : ℕ => -(N : ℂ) + r)
  have hL' : ∀ j, (List.map (fun c => xJ E j - algebraMap ℂ _ c) (L' j)).prod = 0 := by
    intro j
    rw [List.map_map]
    exact hL j
  haveI hBfin : FiniteDimensional ℂ (Subalgebra.toSubmodule B) :=
    TF.fin_adjoin (fun j : Fin m => xJ E j) hxcomm (fun j => ⟨L' j, hL' j⟩)
  have hlift : ∀ u : ℂ, (lift (qdet E u) : Module.End ℂ (TV n M (Fin m))) =
      algebraMap ℂ _ (∏ k, (u + (l k : ℂ))) := by
    intro u
    rw [hl u]
    exact TF.lift_alg _
  have hqB : ∀ u : ℂ, (∀ j : Fin m, ∀ c ∈ L' j, u + c ≠ 0) → qdet (tE Finset.univ E) u ∈ B := by
    intro u hu
    obtain ⟨h, hhB, hh⟩ := TF.left_inv_prod B.toSubring
      (List.ofFn fun j : Fin m => algebraMap ℂ (Module.End ℂ (TV n M (Fin m))) u + xJ E j) (by
        intro a ha
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
        exact TF.inv_of_alg B (xJ E j) (hxB j) u (L' j) (hL' j) (hu j))
    have hstep := hS n M E hE m u
    rw [hlift] at hstep
    have e1 : qdet (tE Finset.univ E) u =
        h * (algebraMap ℂ _ (∏ k, (u + (l k : ℂ))) * PiJ m E (u + 1)) := by
      rw [← hstep, ← mul_assoc, show h * PiJ m E u = 1 from hh, one_mul]
    rw [e1]
    refine B.mul_mem hhB (B.mul_mem (B.algebraMap_mem _) ?_)
    refine Subalgebra.list_prod_mem _ ?_
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact B.add_mem (B.algebraMap_mem _) (hxB j)
  have hinf : {u : ℂ | ∀ j : Fin m, ∀ c ∈ L' j, u + c ≠ 0}.Infinite := by
    refine Set.Infinite.mono ?_
      (Finset.finite_toSet (Finset.univ.biUnion fun j => ((L' j).map (fun c => -c)).toFinset)).infinite_compl
    intro u hu j c hc h
    apply hu
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ _, List.mem_toFinset.mpr (List.mem_map.mpr ⟨c, hc, by linear_combination -h⟩)⟩
  have hqA : ∀ u, qdet (tE Finset.univ E) u ∈ A :=
    TF.qdet_mem _ A (fun a b => Algebra.subset_adjoin ⟨(), a, b, rfl⟩)
  have hcoefmem : ∀ (K : Subalgebra ℂ (Module.End ℂ (TV n M (Fin m)))) (Su : Set ℂ), Su.Infinite →
      (∀ u ∈ Su, qdet (tE Finset.univ E) u ∈ K) → ∀ i ∈ Finset.range (n + 1), c i ∈ K := by
    intro K Su hSu hK i hi
    have := TF.coef (n + 1) (fun i => (Subalgebra.toSubmodule K).mkQ (c i)) Su hSu (by
      intro u hu
      have h1 := hK u hu
      rw [hc u] at h1
      have h2 : (Subalgebra.toSubmodule K).mkQ (∑ i ∈ Finset.range (n + 1), u ^ i • c i) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact h1
      simpa [map_sum, map_smul] using h2) i hi
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hcB : ∀ i ∈ Finset.range (n + 1), c i ∈ B := hcoefmem B _ hinf (fun u hu => hqB u hu)
  have hcA : ∀ i ∈ Finset.range (n + 1), c i ∈ A :=
    hcoefmem A Set.univ Set.infinite_univ (fun u _ => hqA u)
  let p : Polynomial ℂ := ∏ k : Fin n,
    (Polynomial.X + Polynomial.C ((l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ)))
  have hpdeg : p.natDegree < n + 1 := by
    have := Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin n)) (fun k : Fin n =>
      Polynomial.X + Polynomial.C ((l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ)))
    simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at this
    exact lt_of_le_of_lt this (by omega)
  have hpev : ∀ u : ℂ, (∏ k : Fin n, (u + (l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ))) =
      ∑ i ∈ Finset.range (n + 1), p.coeff i * u ^ i := by
    intro u
    rw [← Polynomial.eval_eq_sum_range' hpdeg u]
    simp [p, Polynomial.eval_prod, add_assoc]
  obtain ⟨g, hgB, hg0, hgx, hgq⟩ := hC n M E hE (fun k => (l k : ℂ)) hl ℓ hℓ hW top htop m co
  obtain ⟨c0, hc0⟩ := hCA n M E hE ℓ hW top htop m col b hmono htab
  set φ := ℓ ∘ₗ (LinearMap.proj fun _ : Fin m => top) ∘ₗ g with hφ
  set ρ := ℓ ∘ₗ cA col b with hρ
  have hφc : ∀ i ∈ Finset.range (n + 1), φ ∘ₗ c i - p.coeff i • φ = 0 := by
    refine TF.coef (n + 1) (fun i => φ ∘ₗ c i - p.coeff i • φ) Set.univ Set.infinite_univ ?_
    intro u _
    have h1 := hgq u
    rw [hc u, hpev u, hcs, Finset.sum_smul] at h1
    simp only [LinearMap.comp_smul] at h1
    have h2 := sub_eq_zero.mpr h1
    rw [← Finset.sum_sub_distrib] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub, smul_smul, mul_comm]
  obtain ⟨d, hd0, hd⟩ : ∃ d : ℂ, d ≠ 0 ∧ φ ∘ₗ colD E col = d • φ := by
    unfold colD
    apply TF.eig_prod
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    apply TF.eig_prod
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    split_ifs with hij
    · refine ⟨((l (co i) : ℂ) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℂ)) -
          ((l (co j) : ℂ) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℂ)) + 1, ?_, ?_⟩
      · have h := hcol i j hij.1 hij.2
        have hpos : (0 : ℤ) < (l (co i) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℤ)) -
            (l (co j) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℤ)) + 1 := by
          linarith
        have h3 : ((((l (co i) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℤ)) -
            (l (co j) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℤ)) + 1 : ℤ)) : ℂ) ≠ 0 := by
          exact_mod_cast hpos.ne'
        push_cast at h3
        exact h3
      · rw [LinearMap.comp_add, LinearMap.comp_sub, hgx i, hgx j,
          show φ ∘ₗ (1 : Module.End ℂ (TV n M (Fin m))) = φ from rfl]
        conv_rhs => rw [add_smul, sub_smul, one_smul]
    · exact ⟨1, one_ne_zero, by rw [one_smul]; rfl⟩
  have hcolDB : colD E col ∈ B := by
    unfold colD
    refine Subalgebra.list_prod_mem _ ?_
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    refine Subalgebra.list_prod_mem _ ?_
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    split_ifs
    · exact B.add_mem (B.sub_mem (hxB i) (hxB j)) B.one_mem
    · exact B.one_mem
  have hgc : ∀ v, g (colD E col v) = colD E col (g v) := fun v =>
    LinearMap.congr_fun (hBcomm g hgB _ hcolDB).eq v
  have key : c0 • (ρ ∘ₗ g) = d • φ := by
    rw [← hd]
    refine LinearMap.ext fun v => ?_
    have h1 := LinearMap.congr_fun hc0 (g v)
    rw [hφ, hρ]
    rw [hρ] at h1
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h1 ⊢
    rw [hgc]
    exact h1.symm
  have hc0ne : c0 ≠ 0 := by
    intro h
    apply hg0
    rw [h, zero_smul] at key
    exact (smul_eq_zero.mp key.symm).resolve_left hd0
  have hρg : ρ ∘ₗ g = (c0⁻¹ * d) • φ := by
    rw [mul_smul, ← key, smul_smul, inv_mul_cancel₀ hc0ne, one_smul]
  set Tm : ℕ → Module.End ℂ (TV n M (Fin m)) :=
    fun i => if i < n + 1 then c i - algebraMap ℂ _ (p.coeff i) else 0 with hTm
  have hTmi : ∀ i ∈ Finset.range (n + 1), Tm i = c i - algebraMap ℂ _ (p.coeff i) := by
    intro i hi
    show (if i < n + 1 then c i - algebraMap ℂ _ (p.coeff i) else 0) = _
    exact if_pos (Finset.mem_range.mp hi)
  have hTmB : ∀ i, Tm i ∈ B ∧ Tm i ∈ A := by
    intro i
    by_cases h : i < n + 1
    · rw [hTmi i (Finset.mem_range.mpr h)]
      exact ⟨B.sub_mem (hcB i (Finset.mem_range.mpr h)) (B.algebraMap_mem _),
        A.sub_mem (hcA i (Finset.mem_range.mpr h)) (A.algebraMap_mem _)⟩
    · have e : Tm i = 0 := if_neg h
      rw [e]
      exact ⟨B.zero_mem, A.zero_mem⟩
  have hρgT : ∀ i ∈ Finset.range (n + 1), ρ ∘ₗ (g ∘ₗ Tm i) = 0 := by
    intro i hi
    rw [← LinearMap.comp_assoc, hρg, LinearMap.smul_comp, hTmi i hi, LinearMap.comp_sub,
      Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      show φ ∘ₗ (1 : Module.End ℂ (TV n M (Fin m))) = φ from rfl, hφc i hi, smul_zero]
  obtain ⟨v0, hv0⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg0 (LinearMap.ext h)
  haveI hQfin : FiniteDimensional ℂ (Subalgebra.toSubmodule (B ⊓ A)) :=
    Submodule.finiteDimensional_of_le (S₂ := Subalgebra.toSubmodule B) (fun x hx => hx.1)
  obtain ⟨z, hzZ, hz0, hzT⟩ := TF.common_ker (fun i => TF.rc (Tm i))
    (fun i j => TF.rc_comm _ _ (hBcomm _ (hTmB i).1 _ (hTmB j).1)) (TF.ev (g v0))
    (Finset.range (n + 1)) (Submodule.map (TF.lc ρ) (Subalgebra.toSubmodule (B ⊓ A))) inferInstance
    (by
      intro i _ z hz
      obtain ⟨S, hS, rfl⟩ := Submodule.mem_map.mp hz
      exact Submodule.mem_map.mpr ⟨S * Tm i, (B ⊓ A).mul_mem hS ⟨(hTmB i).1, (hTmB i).2⟩, rfl⟩)
    (by
      intro i hi z hz
      obtain ⟨S, hS, rfl⟩ := Submodule.mem_map.mp hz
      show ρ (S (Tm i (g v0))) = 0
      have hSB : S ∈ B := hS.1
      have h1 : S * (Tm i * g) = g * (Tm i * S) := by
        rw [← mul_assoc, (hBcomm _ (B.mul_mem hSB (hTmB i).1) g hgB).eq, (hBcomm S hSB _ (hTmB i).1).eq]
      have h2 := LinearMap.congr_fun h1 v0
      simp only [Module.End.mul_apply] at h2
      rw [h2]
      have h3 := LinearMap.congr_fun (hρgT i hi) (S v0)
      simpa using h3)
    ⟨TF.lc ρ 1, Submodule.mem_map.mpr ⟨1, (B ⊓ A).one_mem, rfl⟩, by
      show ρ (g v0) ≠ 0
      have h1 := LinearMap.congr_fun hρg v0
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
      rw [h1]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero hc0ne) hd0) hv0⟩
  obtain ⟨S, hS, rfl⟩ := Submodule.mem_map.mp hzZ
  refine ⟨S, hS.2, hz0, fun u => ?_⟩
  show (ρ ∘ₗ S) ∘ₗ qdet (tE Finset.univ E) u = _ • (ρ ∘ₗ S)
  have hψ : ∀ i ∈ Finset.range (n + 1), (ρ ∘ₗ S) ∘ₗ c i = p.coeff i • (ρ ∘ₗ S) := by
    intro i hi
    have h3 : (ρ ∘ₗ S) ∘ₗ Tm i = 0 := hzT i hi
    rw [hTmi i hi, LinearMap.comp_sub, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      sub_eq_zero] at h3
    exact h3
  rw [hc u, hpev u, hcs, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [LinearMap.comp_smul, hψ i hi, smul_smul, mul_comm]
end PositivityTheory.Rg.Cz
