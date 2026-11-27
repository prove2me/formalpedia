-- Prove2me | solution 1 for ReciprocityTheory.Coh.rankLen_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:37:07.800016+00:00
-- url     : https://prove2.me/submissions/6847de05-9642-48ee-8a78-5a53aab81b40

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ProdHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_EqZeroOfLe
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLen
import Theorems.Thm_ReciprocityTheory_Coh_alt_sum_telescope
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_quot_eq
import Theorems.Thm_ReciprocityTheory_Coh_lES_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function TorsionRankLength
open scoped Pointwise
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : RankLenStatement.{u} := by
  intro R _ _ _ t ht L C i p m N hi hses hfg
  obtain ⟨⟨δ, hconn, hles⟩, -⟩ := lES_holds R L L C i p hses
  have hiH : ∀ n, i.H n = (t ^ m) • (LinearMap.id : L.H n →ₗ[R] L.H n) := by
    intro n
    refine LinearMap.ext fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [Cx.Hom.H, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact hi n z.1
  have hrange : ∀ n, LinearMap.range (i.H n) = (t ^ m) • (⊤ : Submodule R (L.H n)) := by
    intro n
    ext x
    rw [hiH, LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hlen : ∀ n, Module.length R (C.H n) =
      Module.length R (QuotSMulTop (t ^ m) (L.H n)) + Module.length R (K (L.H (n + 1)) (t ^ m)) := by
    intro n
    have hexs : Function.Exact (LinearMap.ker (δ n)).subtype (δ n).rangeRestrict := by
      intro y
      constructor
      · intro hy
        refine ⟨⟨y, ?_⟩, rfl⟩
        rw [LinearMap.mem_ker]
        have := congrArg Subtype.val hy
        simpa using this
      · rintro ⟨z, rfl⟩
        apply Subtype.ext
        simpa using z.2
    rw [Module.length_eq_add_of_exact _ _ (LinearMap.ker (δ n)).injective_subtype
      (LinearMap.surjective_rangeRestrict _) hexs]
    congr 1
    · rw [LinearMap.exact_iff.1 (hles.exC n), ← (LinearMap.quotKerEquivRange (p.H n)).length_eq,
        LinearMap.exact_iff.1 (hles.exB n), hrange]
      try rfl
    · rw [← LinearMap.exact_iff.1 (hles.exA n), hiH]
  have hfin : ∀ n, Module.Finite R (L.H n) := hfg.1
  have hq := fun n => @len_quot_eq R _ _ _ (L.H n) _ _ (hfin n) t ht m
  have hKfin : ∀ n, Module.length R (K (L.H n) (t ^ m)) ≠ ⊤ :=
    fun n => ne_top_of_le_ne_top (hq n).2.2 (hq n).2.1
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ → ℕ, kk = fun n => (Module.length R (K (L.H n) (t ^ m))).toNat := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ rr : ℕ → ℕ, rr = fun n => Module.finrank R (L.H n) := ⟨_, rfl⟩
  have hKn : ∀ n, Module.length R (K (L.H n) (t ^ m)) = (kk n : ℕ∞) := by
    intro n; rw [hkk]; exact (ENat.coe_toNat (hKfin n)).symm
  have hCn : ∀ n, Module.length R (C.H n) = ((m * rr n + kk n + kk (n + 1) : ℕ) : ℕ∞) := by
    intro n
    rw [hlen, (hq n).1, hKn, hKn, hrr]
    push_cast
    ring
  have hCnat : ∀ n, (Module.length R (C.H n)).toNat = m * rr n + kk n + kk (n + 1) := by
    intro n; rw [hCn, ENat.toNat_coe]
  have hzero : ∀ n, N < n → kk n = 0 ∧ rr n = 0 := by
    intro n hn
    haveI := hfg.2 n hn
    refine ⟨?_, ?_⟩
    · have h0 : Module.length R (K (L.H n) (t ^ m)) = 0 := Module.length_eq_zero_iff.2 inferInstance
      rw [hKn] at h0
      exact_mod_cast h0
    · rw [hrr]; exact Module.finrank_zero_of_subsingleton
  have hk0 : kk 0 = 0 := by
    have hker : K (L.H 0) (t ^ m) = ⊥ := by
      show LinearMap.ker ((t ^ m) • (LinearMap.id : L.H 0 →ₗ[R] L.H 0)) = ⊥
      rw [← hiH]
      exact LinearMap.ker_eq_bot.2 hles.inj
    have h0 : Module.length R (K (L.H 0) (t ^ m)) = 0 := by
      rw [hker]; exact Module.length_eq_zero_iff.2 inferInstance
    rw [hKn] at h0
    exact_mod_cast h0
  refine ⟨⟨fun n => Module.length_ne_top_iff.1 (by rw [hCn]; exact ENat.coe_ne_top _), fun n hn => ?_⟩,
    ?_, fun n => ⟨?_, ?_⟩⟩
  · apply (Module.length_eq_zero_iff (R := R)).1
    rw [hCn, (hzero n hn).1, (hzero n hn).2, (hzero (n + 1) (by omega)).1]
    simp
  · unfold Cx.chi Cx.chiRk
    simp_rw [hCnat]
    have hterm : ∀ n, (-1 : ℤ) ^ n * ((m * rr n + kk n + kk (n + 1) : ℕ) : ℤ) =
        (m : ℤ) * ((-1) ^ n * (Module.finrank R (L.H n) : ℤ)) + (-1) ^ n * ((kk n : ℤ) + kk (n + 1)) := by
      intro n; rw [hrr]; push_cast; ring
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_add_distrib, ← Finset.mul_sum,
      alt_sum_telescope (fun n => (kk n : ℤ)) N, hk0, (hzero (N + 1) (by omega)).1]
    simp
  · rw [hCnat]
    have h1 : kk n ≤ (Module.length R (Submodule.torsion R (L.H n))).toNat := by
      rw [hkk]; exact ENat.toNat_le_toNat (hq n).2.1 (hq n).2.2
    have h2 : kk (n + 1) ≤ (Module.length R (Submodule.torsion R (L.H (n + 1)))).toNat := by
      rw [hkk]; exact ENat.toNat_le_toNat (hq (n + 1)).2.1 (hq (n + 1)).2.2
    rw [hrr] at *
    simp only at h1 h2 ⊢
    omega
  · rw [hCnat, hrr]
    simp only
    omega
end ReciprocityTheory.Coh
