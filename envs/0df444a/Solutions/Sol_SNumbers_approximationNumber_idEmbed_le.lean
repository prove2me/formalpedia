-- Prove2me | solution 1 for SNumbers.approximationNumber_idEmbed_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:28.073127+00:00
-- url     : https://prove2.me/submissions/1c9ef37c-f268-4af7-954f-bc12347ad750

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
public import Theorems.Thm_SNumbers_piLp_norm_restrict_le
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_ContinuousLinearMap_rank_comp_comp_le
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_padFin_projFin_apply
public import Theorems.Thm_SNumbers_piLp_norm_mono
public import Theorems.Thm_SNumbers_rank_id_piLp
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply


attribute [local simp] SNumbers.idEmbed_apply
section
@[expose] public section
universe u
open scoped ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
private lemma card_filter_ge (n : ℕ) (hn : n ≤ m) :
    (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n)).card = m - n := by
  have hlt : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n)).card = n := by
    rw [show (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n))
          = Finset.univ.image (Fin.castLE hn) from ?_,
      Finset.card_image_of_injective _ (Fin.castLE_injective hn), Finset.card_univ,
      Fintype.card_fin]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi; exact ⟨⟨(i : ℕ), hi⟩, by simp⟩
    · rintro ⟨j, rfl⟩; simp only [Fin.val_castLE]; exact j.isLt
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (p := fun i : Fin m => (i : ℕ) < n)
  rw [hlt, Finset.card_univ, Fintype.card_fin] at hsum
  omega
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
namespace SNumbers
theorem _root_.solution {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n ≤ m) :
    approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n
      ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
  -- The rank-`≤ n` approximant `L = id ∘ Pₙ`, written `B ∘ id_{ℓ^q_n} ∘ A`.
  set A : PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp q (fun _ : Fin n => 𝕜) :=
    projFin hn with hA
  set B : PiLp q (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    (idEmbed p q).comp padFin with hB
  set L := B.comp ((ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin n => 𝕜))).comp A) with hL
  have hLrank : L.rank ≤ (n : Cardinal) :=
    (ContinuousLinearMap.rank_comp_comp_le A _ B).trans_eq (rank_id_piLp n)
  -- The residual zeros the first `n` coordinates.
  have hres : ∀ x : PiLp q (fun _ : Fin m => 𝕜), (idEmbed (𝕜 := 𝕜) (m := m) p q - L) x
      = WithLp.toLp p (fun i : Fin m => if (i : ℕ) < n then 0 else (WithLp.ofLp x) i) := by
    intro x; ext i
    simp only [hL, hA, hB, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, PiLp.sub_apply, idEmbed_apply]
    rw [padFin_projFin_apply]
    by_cases hi : (i : ℕ) < n <;> simp [hi]
  have hbound : ‖idEmbed (𝕜 := 𝕜) (m := m) p q - L‖
      ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
    refine opNorm_le_bound _ (by positivity) fun x => ?_
    rw [hres x]
    set g : Fin m → 𝕜 := fun i => if (i : ℕ) < n then 0 else (WithLp.ofLp x) i with hg
    have hsupp : ∀ i ∉ Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n), g i = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [hg, hi]
    have hmono : ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ ≤ ‖x‖ :=
      piLp_norm_mono fun i => by
        simp only [hg]; split_ifs with h <;> simp
    calc ‖(WithLp.toLp p g : PiLp p (fun _ : Fin m => 𝕜))‖
        ≤ ((Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n)).card : ℝ)
            ^ (1 / p.toReal - 1 / q.toReal) * ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ :=
          piLp_norm_restrict_le hpq hq _ g hsupp
      _ = ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal)
            * ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ := by rw [card_filter_ge n hn]
      _ ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖ := by gcongr
  exact (approximationNumber_le_norm_sub hLrank).trans hbound
end SNumbers
