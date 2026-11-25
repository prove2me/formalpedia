-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AlgRes.isSNC_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:59.420906+00:00
-- url     : https://prove2.me/submissions/5cec8928-0c92-4d36-9b2a-e9232a8a07eb

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
import Theorems.Thm_ReciprocityTheory_AnForm_R_eval_bind_one
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_poly_of_locRing_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_prod_reindex_option
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_isOpen_nonvan
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_coord_mem_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
namespace AlgRes
theorem _root_.solution {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A)
    (idx : R.M → Fin R.n) (hidx : ∀ x, x ∈ R.src (idx x)) (φ : R.M → R.M → ℝ)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a) (hfP : f ∉ P)
    (hz : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) :
    ∃ m : Fin R.rc → ℕ,
      IsSNC A ⟨fun x => R.src (idx x), fun x => R.isOpen_alt_bis (idx x), hidx, φ⟩
        (fun x y => eval (fun q => eval (R.coord (idx x) y) (R.lift (idx x) q)) f) m R.comp := by
  classical
  obtain ⟨m, hm⟩ := R.mult f a hf hfP hz
  refine ⟨m, fun x => ?_⟩
  have hx : x ∈ R.src (idx x) := hidx x
  obtain ⟨u, hu, hfu⟩ := hm (idx x) x hx
  obtain ⟨pa, pb, pc, ha, hb, hc, hI⟩ := exists_poly_of_locRing_eq _ _ (R.coord_mem_zero _ hx)
    _ (∏ l ∈ (R.sncAt (idx x) x hx).J, (R.sncAt (idx x) x hx).r l ^
      ((R.sncAt (idx x) x hx).σ l).elim 0 m) u hu (by rw [hfu, map_prod]; simp only [map_pow])
  obtain ⟨O, hOo, hxO, -, hOc⟩ := R.comp_eq (idx x) x hx
  set d := R.sncAt (idx x) x hx with hd
  have hO' : IsOpen (O ∩ ({y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pa ≠ 0} ∩
      {y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pb ≠ 0} ∩
      {y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pc ≠ 0})) :=
    hOo.inter (((R.isOpen_nonvan _ pa).inter (R.isOpen_nonvan _ pb)).inter (R.isOpen_nonvan _ pc))
  obtain ⟨ψ, hψc, hxψ, hψs, hψe⟩ := hA.2 (idx x) x hx d.r d.span_eq _ hO'
    ⟨hxO, ⟨⟨hx, ha⟩, ⟨hx, hb⟩⟩, ⟨hx, hc⟩⟩
  have hJ : ∀ l k, d.σ l = some k → l ∈ d.J := by
    intro l k hl; by_contra hJ; rw [(d.σ_eq_none l).2 hJ] at hl; cases hl
  let σ' : Fin R.rc → Option (Fin e) := fun k =>
    if h : ∃ l, d.σ l = some k then some (Classical.choose h) else none
  have hσ' : ∀ k l, σ' k = some l ↔ d.σ l = some k := by
    intro k l
    by_cases h : ∃ l, d.σ l = some k
    · have hc0 := Classical.choose_spec h
      simp only [σ', dif_pos h, Option.some.injEq]
      constructor
      · rintro rfl; exact hc0
      · intro hl
        exact d.σ_injOn (hJ _ _ hc0) (hJ _ _ hl) (by rw [hc0, hl])
    · simp only [σ', dif_neg h]
      constructor
      · intro h'; cases h'
      · intro hl; exact absurd ⟨l, hl⟩ h
  refine ⟨ψ, hψc, hxψ, fun y hy => (hψs hy).2, σ', ?_, ?_,
    fun y => eval (R.coord (idx x) y) pa / eval (R.coord (idx x) y) pb, ?_, ?_, ?_⟩
  · intro k k' l h1 h2
    rw [hσ'] at h1 h2
    rw [h1] at h2
    exact Option.some.inj h2
  · intro k
    ext y
    constructor
    · rintro ⟨hyk, hyψ⟩
      have hyO : y ∈ R.comp k ∩ O := ⟨hyk, (hψs hyψ).1.1⟩
      rw [hOc k] at hyO
      obtain ⟨-, l, hl, h0⟩ := hyO
      refine ⟨hyψ, l, (hσ' k l).2 hl, ?_⟩
      rw [hψe y hyψ]; exact h0
    · rintro ⟨hyψ, l, hl, h0⟩
      refine ⟨?_, hyψ⟩
      have hyO : y ∈ {y ∈ O | ∃ l, d.σ l = some k ∧ eval (R.coord (idx x) y) (d.r l) = 0} := by
        refine ⟨(hψs hyψ).1.1, l, (hσ' k l).1 hl, ?_⟩
        rw [hψe y hyψ] at h0; exact h0
      rw [← hOc k] at hyO
      exact hyO.1
  · intro j z hz
    have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src (idx x) :=
      ⟨hz.1, (hψs hz.2).2⟩
    have h1 := hA.1 (idx x) pa j z hz'
    have h2 := hA.1 (idx x) pb j z hz'
    exact h1.div h2 (hψs hz.2).1.2.1.2.2
  · intro y hy
    exact div_ne_zero (hψs hy).1.2.1.1.2 (hψs hy).1.2.1.2.2
  · intro y hy
    have hyO := (hψs hy).1
    have hyz := R.coord_mem_zero (idx x) (hψs hy).2 _ hI
    have hcy : eval (R.coord (idx x) y) pc ≠ 0 := hyO.2.2.2
    have hby : eval (R.coord (idx x) y) pb ≠ 0 := hyO.2.1.2.2
    simp only [map_mul, map_sub] at hyz
    have hyz' := (mul_eq_zero.1 hyz).resolve_left hcy
    rw [sub_eq_zero] at hyz'
    have hF : eval (R.coord (idx x) y) (bind₁ (R.lift (idx x)) f) =
        eval (R.coord (idx x) y) pa / eval (R.coord (idx x) y) pb *
          eval (R.coord (idx x) y) (∏ l ∈ d.J, d.r l ^ (d.σ l).elim 0 m) := by
      rw [div_mul_eq_mul_div, eq_div_iff hby]
      linear_combination hyz'
    have hG : eval (R.coord (idx x) y) (∏ l ∈ d.J, d.r l ^ (d.σ l).elim 0 m) =
        ∏ k, Option.elim (σ' k) 1 (fun i => eval (R.coord (idx x) y) (d.r i) ^ m k) := by
      rw [map_prod]; simp only [map_pow]
      exact prod_reindex_option d.J d.σ d.σ_eq_none σ' hσ' m (fun l => eval (R.coord (idx x) y) (d.r l))
    show eval _ f = _
    rw [← eval_bind_one, hF, hG]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hψe y hy]
    rcases σ' k with _ | l <;> rfl
end AlgRes
end ReciprocityTheory.AnForm.R
