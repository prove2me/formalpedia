-- Prove2me | solution 1 for PI.SqPairLocal.glue_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:59.772377+00:00
-- url     : https://prove2.me/submissions/1dea056b-9674-4b9b-9954-d33a32797c40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_pres_add
import Theorems.Thm_PI_SqPairLocal_pres_sub
import Theorems.Thm_PI_SqPairLocal_pres_smul
import Theorems.Thm_PI_SqPairLocal_comap_cj_comap
import Theorems.Thm_PI_SqPairLocal_cj_mem_pow
import Theorems.Thm_PI_SqPairLocal_powLoc_fin
import Theorems.Thm_PI_SqPairLocal_good_pert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (hP : PowLoc) {L' L'' : Submodule (𝓞 E) (Fin N → E)} (h' : IsSDG E N L')
    (h'' : IsSDG E N L'') {c : 𝓞 E} (hc : c ≠ 0) (A B : Finset (Ideal (𝓞 E)))
    (hAm : ∀ P ∈ A, P.IsMaximal) (hBm : ∀ P ∈ B, P.IsMaximal)
    (hA : ∀ P ∈ A, P.comap (cj E) ∈ A) (hB : ∀ P ∈ B, P.comap (cj E) ∈ B)
    {e₁ e₂ : Matrix (Fin N) (Fin N) E} (p₁' : Pres L' e₁) (p₁'' : Pres L'' e₁)
    (p₂' : Pres L' e₂) (p₂'' : Pres L'' e₂)
    (g₁ : ∀ P ∈ A, Good P c L' L'' e₁) (g₂ : ∀ P ∈ B, Good P c L' L'' e₂) :
    ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧ ∀ P ∈ A ∪ B, Good P c L' L'' e := by
  classical
  obtain ⟨K, hK⟩ := powLoc_fin hP (A ∪ B)
    (fun P h => (Finset.mem_union.mp h).elim (hAm P) (hBm P)) hc
  have hcop : IsCoprime (∏ P ∈ A, P ^ K) (∏ P ∈ B \ A, P ^ K) := by
    refine IsCoprime.prod_left fun P hPA => IsCoprime.prod_right fun P' hP' => ?_
    have hne : P ≠ P' := fun h => (Finset.mem_sdiff.mp hP').2 (h ▸ hPA)
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      ((hAm P hPA).coprime_of_ne (hBm P' (Finset.mem_sdiff.mp hP').1) hne)).pow
  have h1 : (1 : 𝓞 E) ∈ (∏ P ∈ A, P ^ K) ⊔ ∏ P ∈ B \ A, P ^ K := by
    rw [Ideal.isCoprime_iff_sup_eq.mp hcop]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  have memA : ∀ P ∈ A, a ∈ P ^ K := fun P h => by
    first
      | exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun Q => Q ^ K) h) ha
      | exact Ideal.prod_le_inf.trans (Finset.inf_le h) ha
  have memB : ∀ P ∈ B \ A, b ∈ P ^ K := fun P h => by
    first
      | exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun Q => Q ^ K) h) hb
      | exact Ideal.prod_le_inf.trans (Finset.inf_le h) hb
  have hab' : (a : E) + (b : E) = 1 := by exact_mod_cast hab
  have hnb : ((-b : 𝓞 E) : E) = -(b : E) := by
    first
      | rfl
      | push_cast; ring
      | simp
  have heq : e₁ + (a : E) • (e₂ - e₁) = e₂ + ((-b : 𝓞 E) : E) • (e₂ - e₁) := by
    rw [hnb, eq_sub_of_add_eq hab', sub_smul, one_smul, neg_smul]
    abel
  refine ⟨e₁ + (a : E) • (e₂ - e₁), pres_add p₁' (pres_smul a (pres_sub p₂' p₁')),
    pres_add p₁'' (pres_smul a (pres_sub p₂'' p₁'')), fun P hPU => ?_⟩
  by_cases hPA : P ∈ A
  · haveI := (hAm P hPA).isPrime
    exact good_pert h' h'' (g₁ P hPA) p₁' p₁'' (pres_sub p₂' p₁') (pres_sub p₂'' p₁'')
      (hK P (Finset.mem_union_left _ hPA) a (memA P hPA))
      (hK P (Finset.mem_union_left _ hPA) _ (cj_mem_pow (memA _ (hA P hPA))))
  · have hPB : P ∈ B := (Finset.mem_union.mp hPU).resolve_left hPA
    have hPBA : P ∈ B \ A := Finset.mem_sdiff.mpr ⟨hPB, hPA⟩
    have hcB : P.comap (cj E) ∈ B \ A := by
      refine Finset.mem_sdiff.mpr ⟨hB P hPB, fun h => hPA ?_⟩
      have h2 := hA _ h
      rwa [comap_cj_comap] at h2
    haveI := (hBm P hPB).isPrime
    rw [heq]
    exact good_pert h' h'' (g₂ P hPB) p₂' p₂'' (pres_sub p₂' p₁') (pres_sub p₂'' p₁'')
      (hK P (Finset.mem_union_right _ hPB) _ (neg_mem (memB P hPBA)))
      (hK P (Finset.mem_union_right _ hPB) _ (cj_mem_pow (neg_mem (memB _ hcB))))
end PI.SqPairLocal
