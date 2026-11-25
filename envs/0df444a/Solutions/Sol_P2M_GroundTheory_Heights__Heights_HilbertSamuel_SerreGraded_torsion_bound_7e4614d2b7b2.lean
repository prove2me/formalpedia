-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_torsion_bound_7e4614d2b7b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:22.422823+00:00
-- url     : https://prove2.me/submissions/37c642c0-2f61-46a5-8ea9-9e081506f119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_X_5d3e9f420ff7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_monomial_d086f0f1a946
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_eq_af68eef4f60e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_coeff_shifted_a179fd9cccd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_exists_common_b30485fec4df

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) (u : Fin q) :
    ∃ E : ℕ, ∀ m ∈ gradedModule q d t,
      (∀ j, w j ≠ 0 → ∃ D : ℕ,
        (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) • m ∈ shifted w d t u) →
      ∀ k, E ≤ k → ∃ z ∈ gradedSpan w d t k, m.coeff (k + 1) = w u * z := by
  classical
  set N := shifted w d t u with hN
  have hpow : ∀ (j : Fin q) (g : Polynomial Ω) (D : ℕ),
      (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) • g ∈ N → ∀ D', D ≤ D' →
      (MvPolynomial.X j ^ D' : MvPolynomial (Fin q) ℤ) • g ∈ N := by
    intro j g D h D' hD'
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hD'
    rw [pow_add, mul_comm, mul_smul]
    exact N.smul_mem _ h
  let Γ : Submodule (MvPolynomial (Fin q) ℤ) (Polynomial Ω) :=
    { carrier := {m | m ∈ gradedModule q d t ∧
        ∀ j, w j ≠ 0 → ∃ D : ℕ, (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) • m ∈ N}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun j hj => ?_⟩
        obtain ⟨D₁, h₁⟩ := ha' j hj
        obtain ⟨D₂, h₂⟩ := hb' j hj
        refine ⟨D₁ + D₂, ?_⟩
        rw [smul_add]
        exact add_mem (hpow j a D₁ h₁ _ (by omega)) (hpow j b D₂ h₂ _ (by omega))
      zero_mem' := ⟨zero_mem _, fun j _ => ⟨0, by simp⟩⟩
      smul_mem' := by
        rintro c m ⟨hm, hm'⟩
        refine ⟨Submodule.smul_mem _ c hm, fun j hj => ?_⟩
        obtain ⟨D, hD⟩ := hm' j hj
        refine ⟨D, ?_⟩
        rw [← mul_smul, mul_comm, mul_smul]
        exact N.smul_mem c hD }
  have hMfg : (gradedModule q d t).FG := by
    refine ⟨Finset.univ.image (fun l => C (t l) * X ^ d l), ?_⟩
    rw [gradedModule, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hNoeth : IsNoetherian (MvPolynomial (Fin q) ℤ) (gradedModule q d t) :=
    isNoetherian_of_fg_of_noetherian _ hMfg
  obtain ⟨S, hS⟩ : Γ.FG := isNoetherian_submodule.mp hNoeth Γ (fun m hm => hm.1)
  have hgen : ∀ g ∈ S, g ∈ Γ := fun g hg => by
    rw [← hS]; exact Submodule.subset_span (by exact_mod_cast hg)
  obtain ⟨Dm, hDm⟩ := exists_common (S ×ˢ (Finset.univ : Finset (Fin q)))
    (fun p D => (MvPolynomial.X p.2 ^ D : MvPolynomial (Fin q) ℤ) • p.1 ∈ N) (by
      rintro ⟨g, j⟩ hgj
      rw [Finset.mem_product] at hgj
      by_cases hj : w j = 0
      · refine ⟨1, fun D' hD' => hpow j g 1 ?_ D' hD'⟩
        rw [pow_one, smul_eq w hA, act_X, hj, map_zero, zero_mul, zero_mul]
        exact zero_mem _
      · obtain ⟨D, hD⟩ := (hgen g hgj.1).2 j hj
        exact ⟨D, hpow j g D hD⟩)
  refine ⟨q * Dm + S.sup natDegree, fun m hm htors k hk => ?_⟩
  have hmΓ : m ∈ Γ := ⟨hm, htors⟩
  rw [← hS, Submodule.mem_span_finset] at hmΓ
  obtain ⟨f, -, rfl⟩ := hmΓ
  suffices hT : (∑ g ∈ S, f g • g).coeff (k + 1) ∈
      (gradedSpan w d t k).map (AddMonoidHom.mulLeft (w u)) by
    obtain ⟨z, hz, hz'⟩ := AddSubgroup.mem_map.mp hT
    exact ⟨z, hz, hz'.symm⟩
  rw [finsetSum_coeff]
  refine AddSubgroup.sum_mem _ fun g hg => ?_
  rw [MvPolynomial.as_sum (f g), Finset.sum_smul, finsetSum_coeff]
  refine AddSubgroup.sum_mem _ fun v _ => ?_
  by_cases hlow : ∀ j, v j < Dm
  · have hdeg : (MvPolynomial.monomial v (MvPolynomial.coeff v (f g)) • g).natDegree < k + 1 := by
      rw [smul_eq w hA, act_monomial]
      have h1 := natDegree_mul_le (p := C (((MvPolynomial.coeff v (f g) : ℤ) : Ω) * ∏ j, w j ^ v j) *
        X ^ (∑ j, v j)) (q := g)
      have h2 := natDegree_C_mul_X_pow_le (((MvPolynomial.coeff v (f g) : ℤ) : Ω) * ∏ j, w j ^ v j)
        (∑ j, v j)
      have h3 : ∑ j, v j ≤ q * Dm := by
        calc ∑ j, v j ≤ ∑ _j : Fin q, Dm := Finset.sum_le_sum fun j _ => (hlow j).le
          _ = q * Dm := by simp
      have h4 : g.natDegree ≤ S.sup natDegree := Finset.le_sup (f := natDegree) hg
      omega
    rw [coeff_eq_zero_of_natDegree_lt hdeg]
    exact zero_mem _
  · simp only [not_forall, not_lt] at hlow
    obtain ⟨j, hj⟩ := hlow
    have hsplit : MvPolynomial.monomial v (MvPolynomial.coeff v (f g)) =
        MvPolynomial.monomial (v - Finsupp.single j Dm) (MvPolynomial.coeff v (f g)) *
          MvPolynomial.X j ^ Dm := by
      rw [← MvPolynomial.monomial_add_single, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)]
    rw [hsplit, mul_smul]
    obtain ⟨z, hz, hz'⟩ := coeff_shifted w d t hA u
      (N.smul_mem _ (hDm (g, j) (Finset.mem_product.mpr ⟨hg, Finset.mem_univ j⟩))) k
    rw [hz']
    exact AddSubgroup.mem_map.mpr ⟨z, hz, rfl⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
