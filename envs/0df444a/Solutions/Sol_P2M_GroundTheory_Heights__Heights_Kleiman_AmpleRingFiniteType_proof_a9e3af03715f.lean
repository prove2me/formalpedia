-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_proof_a9e3af03715f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:01:36.60881+00:00
-- url     : https://prove2.me/submissions/88266234-3a7e-4b8b-a354-4d57f1b1f130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartGens_mem_8cd9915ac670
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_ampleChart_le_64c0456cd574
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_exists_pow_mul_mem_ampleRing_e62ddd67ef9a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open AmpleRingFiniteType
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace AmpleRingFiniteType
theorem _root_.solution : AmpleRingFiniteType.Statement := by
  intro S _ N Ω _ _ x H D j h0
  classical
  have hh : ∀ I : Chart x, D.h j ∈ (H.pow D.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (D.mem_secs j) I
  obtain ⟨n, a, c, J, ha, hc, hsum, hrat⟩ := D.affine j h0
  have hgen : ∀ k, ∀ y ∈ chartGens (J k),
      ∃ M : ℕ, c k ^ M * y ∈ ampleRing H.toSubSystem D.m (D.h j) := fun k y hy =>
    exists_pow_mul_mem_ampleRing H hh (hc k) (J k) (hrat k) (chartGens_mem (J k) y hy)
  choose! M hM using hgen
  set T : Finset Ω := Finset.univ.image a ∪ Finset.univ.image c ∪
    Finset.univ.biUnion (fun k => (chartGens (J k)).image fun y => c k ^ M k y * y) with hTdef
  have haT : ∀ k, a k ∈ T := fun k =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  have hcT : ∀ k, c k ∈ T := fun k =>
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  have hyT : ∀ k, ∀ y ∈ chartGens (J k), c k ^ M k y * y ∈ T := fun k y hy =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hy⟩)
  have hTR : ∀ t ∈ T, t ∈ ampleRing H.toSubSystem D.m (D.h j) := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht
        exact ha k
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht
        exact hc k
    · obtain ⟨k, -, ht⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
      exact hM k y hy
  refine ⟨T.card, fun t => (T.equivFin.symm t : Ω), fun t => hTR _ (T.equivFin.symm t).2, ?_⟩
  set K := Algebra.adjoin S (Set.range (fun l => D.h l / D.h j) ∪ (T : Set Ω)) with hKdef
  have hrange : Set.range (fun t => (T.equivFin.symm t : Ω)) = (T : Set Ω) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact (T.equivFin.symm t).2
    · intro hz
      exact ⟨T.equivFin ⟨z, hz⟩, by simp⟩
  have hK : K ≤ (Algebra.adjoin (ampleBase (S := S) D.h j)
      (Set.range fun t => (T.equivFin.symm t : Ω))).restrictScalars S := by
    rw [hrange, Algebra.adjoin_le_iff]
    rintro z (⟨l, rfl⟩ | hz)
    · exact (Subalgebra.mem_restrictScalars _).mpr (Subalgebra.algebraMap_mem _
        (⟨_, Algebra.subset_adjoin ⟨l, rfl⟩⟩ : ampleBase (S := S) D.h j))
    · exact (Subalgebra.mem_restrictScalars _).mpr (Algebra.subset_adjoin hz)
  have hTK : ∀ t ∈ T, t ∈ K := fun t ht => Algebra.subset_adjoin (Or.inr (Finset.mem_coe.mpr ht))
  intro f hf
  apply hK

  have hk : ∀ k, ∃ E : ℕ, c k ^ E * f ∈ K := by
    intro k
    have hcK : c k ∈ K := hTK _ (hcT k)
    have hfJ := ampleChart_le H D j h0 (J k) (Set.mem_iInter.mp hf (J k))
    clear hf
    induction hfJ using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨l, rfl⟩ | hz
      · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin (Or.inl ⟨l, rfl⟩)⟩
      · exact ⟨M k z, hTK _ (hyT k z (Finset.mem_coe.mp hz))⟩
    | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem K r⟩
    | add z z' _ _ h1 h2 =>
      obtain ⟨E, hE⟩ := h1
      obtain ⟨E', hE'⟩ := h2
      refine ⟨E + E', ?_⟩
      have e1 : c k ^ (E + E') * (z + z') = c k ^ E' * (c k ^ E * z) + c k ^ E * (c k ^ E' * z') := by
        ring
      rw [e1]
      exact add_mem (mul_mem (pow_mem hcK _) hE) (mul_mem (pow_mem hcK _) hE')
    | mul z z' _ _ h1 h2 =>
      obtain ⟨E, hE⟩ := h1
      obtain ⟨E', hE'⟩ := h2
      refine ⟨E + E', ?_⟩
      have e1 : c k ^ (E + E') * (z * z') = (c k ^ E * z) * (c k ^ E' * z') := by ring
      rw [e1]
      exact mul_mem hE hE'
  choose E hE using hk
  set E₀ := Finset.univ.sup E with hE₀
  have hbig : ∀ k, c k ^ E₀ * f ∈ K := by
    intro k
    have hle : E k ≤ E₀ := Finset.le_sup (Finset.mem_univ k)
    have e1 : c k ^ E₀ * f = c k ^ (E₀ - E k) * (c k ^ E k * f) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [e1]
    exact mul_mem (pow_mem (hTK _ (hcT k)) _) (hE k)

  let cK : Fin n → K := fun k => ⟨c k, hTK _ (hcT k)⟩
  let aK : Fin n → K := fun k => ⟨a k, hTK _ (haT k)⟩
  have hspan : Ideal.span (Set.range cK) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : K) = ∑ k, aK k * cK k := Subtype.ext (by simp [aK, cK, hsum])
    rw [e1]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  let Iid : Ideal K :=
    { carrier := {y | (y : Ω) * f ∈ K}
      add_mem' := fun {y y'} hy hy' => by
        simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, add_mul] at *
        exact add_mem hy hy'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]
        exact zero_mem K
      smul_mem' := fun b y hy => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul, mul_assoc] at *
        exact mul_mem b.2 hy }
  have hle : Ideal.span ((fun y : K => y ^ E₀) '' Set.range cK) ≤ Iid := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    show ((cK k ^ E₀ : K) : Ω) * f ∈ K
    simpa [cK] using hbig k
  rw [Ideal.span_pow_eq_top _ hspan E₀, top_le_iff] at hle
  have h1 : (1 : K) ∈ Iid := hle ▸ Submodule.mem_top
  simpa [Iid] using h1
end AmpleRingFiniteType
end GroundTheory.Heights₂.Heights.Kleiman
