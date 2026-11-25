-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_exists_minor_not_mem_0177843e1511
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:03.717818+00:00
-- url     : https://prove2.me/submissions/e0178d31-c612-4ff4-a2e3-0be8392ef997

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_add_71b7a804ca0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_mul_42b9d2eba7a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mem_of_forall_pow_mul_mem_0c53fdd73f20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_pow_mul_mem_of_le_6554d47dcac9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
theorem _root_.solution (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0)
    (q : Ideal (chartRing ℤ x i)) (hq : q.IsPrime) :
    ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, ∃ ψ ∈ T.dualLat B i, ∃ ψ' ∈ T.dualLat B i,
      ∃ m : chartRing ℤ x i, m ∉ q ∧ (m : Ω) = ψ u * ψ' w - ψ w * ψ' u := by
  classical
  obtain ⟨K, fs, cs, hf, hc, hsum, hb⟩ := B.frame i hi
  choose bs hli hsp hiff using hb
  obtain ⟨l₀, hl₀⟩ : ∃ l, (⟨fs l, hf l⟩ : chartRing ℤ x i) ∉ q := by
    by_contra h
    push Not at h
    apply hq.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : chartRing ℤ x i) = ∑ l, (⟨cs l, hc l⟩ : chartRing ℤ x i) * ⟨fs l, hf l⟩ :=
      Subtype.ext (by simp [hsum])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h l)
  have hgen : ∀ l j, ∃ n : ℕ, fs l ^ n • bs l j ∈ B.lat i := by
    intro l j
    refine (hiff l (bs l j)).2 ⟨Pi.single j 1, fun j' => ⟨0, ?_⟩, ?_⟩
    · rcases eq_or_ne j' j with rfl | h
      · simp
      · simp [h]
    · simp [Pi.single_apply]
  choose n hn using hgen
  let bB : Module.Basis (Fin 2) Ω E := Module.Basis.mk (hli l₀) (hsp l₀).ge
  have hbB : ⇑bB = bs l₀ := Module.Basis.coe_mk _ _
  have hcoord : ∀ p : Fin K × Fin 2 × Fin 2, ∃ mm : ℕ,
      fs l₀ ^ mm * bB.repr (fs p.1 ^ n p.1 p.2.1 • bs p.1 p.2.1) p.2.2 ∈ chartRing ℤ x i := by
    rintro ⟨l, j, j'⟩
    obtain ⟨a, ha, hv⟩ := (hiff l₀ _).1 ⟨0, by simpa using hn l j⟩
    have : bB.repr (fs l ^ n l j • bs l j) = a := by
      rw [hv, ← hbB]
      exact bB.repr_sum_self a
    rw [this]
    exact ha j'
  choose mm hmm using hcoord
  have hbound : ∀ v ∈ B.lat i, ∀ j', fs l₀ ^ Finset.univ.sup mm * bB.repr v j' ∈ chartRing ℤ x i := by
    intro v hv j'
    refine DiagonalForms.mem_of_forall_pow_mul_mem _ fs cs hf hc hsum fun l => ?_
    obtain ⟨a, ha, hva⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
    have hterm : ∀ j, ∃ t : ℕ, fs l ^ t * (a j * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l j) j')) ∈
        chartRing ℤ x i := by
      intro j
      refine DiagonalForms.loc_mul (ha j) ⟨n l j, ?_⟩
      have h1 := DiagonalForms.pow_mul_mem_of_le (hf l₀)
        (Finset.le_sup (f := mm) (Finset.mem_univ (l, j, j'))) (hmm (l, j, j'))
      have h2 : fs l ^ n l j * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l j) j') =
          fs l₀ ^ Finset.univ.sup mm * bB.repr (fs l ^ n l j • bs l j) j' := by
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        ring
      rw [h2]
      exact h1
    have hsplit : fs l₀ ^ Finset.univ.sup mm * bB.repr v j' =
        a 0 * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l 0) j') +
          a 1 * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l 1) j') := by
      rw [hva, Fin.sum_univ_two, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsplit]
    exact DiagonalForms.loc_add (hf l) (hterm 0) (hterm 1)
  have hψ : ∀ j (v : E), (fs l₀ ^ Finset.univ.sup mm • bB.coord j) v =
      fs l₀ ^ Finset.univ.sup mm * bB.repr v j := fun j v => by
    simp [Module.Basis.coord_apply]
  refine ⟨fs l₀ ^ n l₀ 0 • bB 0, by rw [hbB]; exact hn l₀ 0, fs l₀ ^ n l₀ 1 • bB 1, by rw [hbB]; exact hn l₀ 1,
    fs l₀ ^ Finset.univ.sup mm • bB.coord 0, fun v hv => by rw [hψ]; exact hbound v hv 0,
    fs l₀ ^ Finset.univ.sup mm • bB.coord 1, fun v hv => by rw [hψ]; exact hbound v hv 1,
    ⟨fs l₀, hf l₀⟩ ^ (2 * Finset.univ.sup mm + n l₀ 0 + n l₀ 1), fun h => hl₀ (hq.mem_of_pow_mem _ h), ?_⟩
  rw [hψ, hψ, hψ, hψ]
  simp
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
