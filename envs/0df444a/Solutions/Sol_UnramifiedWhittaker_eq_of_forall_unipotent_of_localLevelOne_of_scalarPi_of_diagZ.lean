-- Prove2me | solution 1 for UnramifiedWhittaker.eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/84dffcdb-9213-54fe-8909-a9ce5d3822d2

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

noncomputable section

namespace SlSph

open WithZero

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev Fv : Type := v.adicCompletion ℚ

abbrev mat (g : GL (Fin 2) (Fv v)) : Matrix (Fin 2) (Fin 2) (Fv v) := (g : Matrix (Fin 2) (Fin 2) (Fv v))

def lowerU (c : Fv v) : GL (Fin 2) (Fv v) :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def wK : GL (Fin 2) (Fv v) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def dg (α δ : Fv v) (hα : α ≠ 0) (hδ : δ ≠ 0) : GL (Fin 2) (Fv v) :=
  ⟨!![α, 0; 0, δ], !![α⁻¹, 0; 0, δ⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hα, hδ],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hα, hδ]⟩

theorem mat_unipotent (x : Fv v) : mat v (unipotent x) = !![1, x; 0, 1] := rfl
theorem mat_scalarPi (π : Fv v) (hπ : π ≠ 0) : mat v (scalarPi π hπ) = !![π, 0; 0, π] := rfl
theorem mat_diagZ (π : Fv v) (hπ : π ≠ 0) (m : ℤ) : mat v (diagZ π hπ m) = !![π ^ m, 0; 0, 1] := rfl
theorem mat_lowerU (c : Fv v) : mat v (lowerU v c) = !![1, 0; c, 1] := rfl
theorem mat_lowerU_inv (c : Fv v) : mat v (lowerU v c)⁻¹ = !![1, 0; -c, 1] := rfl
theorem mat_wK : mat v (wK v) = !![0, 1; 1, 0] := rfl
theorem mat_wK_inv : mat v (wK v)⁻¹ = !![0, 1; 1, 0] := rfl
theorem mat_dg (α δ : Fv v) (hα : α ≠ 0) (hδ : δ ≠ 0) : mat v (dg v α δ hα hδ) = !![α, 0; 0, δ] := rfl
theorem mat_dg_inv (α δ : Fv v) (hα : α ≠ 0) (hδ : δ ≠ 0) : mat v (dg v α δ hα hδ)⁻¹ = !![α⁻¹, 0; 0, δ⁻¹] := rfl

theorem mem_K {k : GL (Fin 2) (Fv v)} (h1 : ∀ i j, Valued.v (mat v k i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (mat v k⁻¹ i j) ≤ 1) : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have hsub : ∀ x : Fv v, Valued.v x ≤ 1 → Valued.v (x - 1) ≤ 1 := fun x hx =>
    (Valuation.map_sub _ _ _).trans (max_le hx (le_of_eq (Valuation.map_one _)))
  refine ⟨⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (h1 i j), ?_, ?_⟩,
    ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (h2 i j), ?_, ?_⟩⟩
  · rw [AdelicLevel.idealBound_top]; exact h1 1 0
  · rw [AdelicLevel.idealBound_top]; exact hsub _ (h1 1 1)
  · rw [AdelicLevel.idealBound_top]; exact h2 1 0
  · rw [AdelicLevel.idealBound_top]; exact hsub _ (h2 1 1)

theorem v_zero_le : Valued.v (0 : Fv v) ≤ 1 := by rw [map_zero]; exact zero_le'
theorem v_one_le : Valued.v (1 : Fv v) ≤ 1 := by rw [map_one]

theorem lowerU_mem {c : Fv v} (hc : Valued.v c ≤ 1) : lowerU v c ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  have hc' : Valued.v (-c) ≤ 1 := by rwa [Valuation.map_neg]
  refine mem_K v (fun i j => ?_) (fun i j => ?_)
  · rw [mat_lowerU]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact v_one_le v | exact v_zero_le v | exact hc
  · rw [mat_lowerU_inv]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact v_one_le v | exact v_zero_le v | exact hc'

theorem wK_mem : wK v ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  refine mem_K v (fun i j => ?_) (fun i j => ?_)
  · rw [mat_wK]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact v_one_le v | exact v_zero_le v
  · rw [mat_wK_inv]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact v_one_le v | exact v_zero_le v

theorem dg_mem {u₁ u₂ : Fv v} (h₁ : Valued.v u₁ = 1) (h₂ : Valued.v u₂ = 1) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    dg v u₁ u₂ hu₁ hu₂ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  have h₁' : Valued.v u₁⁻¹ ≤ 1 := by rw [map_inv₀, h₁, inv_one]
  have h₂' : Valued.v u₂⁻¹ ≤ 1 := by rw [map_inv₀, h₂, inv_one]
  refine mem_K v (fun i j => ?_) (fun i j => ?_)
  · rw [mat_dg]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact v_zero_le v | exact h₁.le | exact h₂.le
  · rw [mat_dg_inv]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact v_zero_le v | exact h₁' | exact h₂'

theorem det_eq (g : GL (Fin 2) (Fv v)) :
    (mat v g).det = mat v g 0 0 * mat v g 1 1 - mat v g 0 1 * mat v g 1 0 := Matrix.det_fin_two _

theorem det_ne_zero (g : GL (Fin 2) (Fv v)) : (mat v g).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero

theorem decomp_d (g : GL (Fin 2) (Fv v)) (hd : mat v g 1 1 ≠ 0)
    (hα : (mat v g 0 0 * mat v g 1 1 - mat v g 0 1 * mat v g 1 0) / mat v g 1 1 ≠ 0) :
    g = unipotent (mat v g 0 1 / mat v g 1 1) *
      dg v ((mat v g 0 0 * mat v g 1 1 - mat v g 0 1 * mat v g 1 0) / mat v g 1 1) (mat v g 1 1) hα hd *
      lowerU v (mat v g 1 0 / mat v g 1 1) := by
  apply Units.ext
  change mat v g = mat v _
  rw [show mat v (unipotent (mat v g 0 1 / mat v g 1 1) *
      dg v ((mat v g 0 0 * mat v g 1 1 - mat v g 0 1 * mat v g 1 0) / mat v g 1 1) (mat v g 1 1) hα hd *
      lowerU v (mat v g 1 0 / mat v g 1 1)) =
      mat v (unipotent (mat v g 0 1 / mat v g 1 1)) *
      mat v (dg v ((mat v g 0 0 * mat v g 1 1 - mat v g 0 1 * mat v g 1 0) / mat v g 1 1) (mat v g 1 1) hα hd) *
      mat v (lowerU v (mat v g 1 0 / mat v g 1 1)) from rfl,
    mat_unipotent, mat_dg, mat_lowerU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem decomp_c (g : GL (Fin 2) (Fv v)) (hc : mat v g 1 0 ≠ 0)
    (hα : (mat v g 0 1 * mat v g 1 0 - mat v g 0 0 * mat v g 1 1) / mat v g 1 0 ≠ 0) :
    g = unipotent (mat v g 0 0 / mat v g 1 0) *
      dg v ((mat v g 0 1 * mat v g 1 0 - mat v g 0 0 * mat v g 1 1) / mat v g 1 0) (mat v g 1 0) hα hc *
      (lowerU v (mat v g 1 1 / mat v g 1 0) * wK v) := by
  apply Units.ext
  change mat v g = mat v _
  rw [show mat v (unipotent (mat v g 0 0 / mat v g 1 0) *
      dg v ((mat v g 0 1 * mat v g 1 0 - mat v g 0 0 * mat v g 1 1) / mat v g 1 0) (mat v g 1 0) hα hc *
      (lowerU v (mat v g 1 1 / mat v g 1 0) * wK v)) =
      mat v (unipotent (mat v g 0 0 / mat v g 1 0)) *
      mat v (dg v ((mat v g 0 1 * mat v g 1 0 - mat v g 0 0 * mat v g 1 1) / mat v g 1 0) (mat v g 1 0) hα hc) *
      (mat v (lowerU v (mat v g 1 1 / mat v g 1 0)) * mat v (wK v)) from rfl,
    mat_unipotent, mat_dg, mat_lowerU, mat_wK]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem iwasawa (g : GL (Fin 2) (Fv v)) :
    ∃ (x α δ : Fv v) (hα : α ≠ 0) (hδ : δ ≠ 0) (k : GL (Fin 2) (Fv v)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ ∧ g = unipotent x * dg v α δ hα hδ * k := by
  have hdet := det_ne_zero v g
  rw [det_eq] at hdet
  by_cases hcd : Valued.v (mat v g 1 0) ≤ Valued.v (mat v g 1 1)
  ·
    have hd : mat v g 1 1 ≠ 0 := by
      intro hd
      have : Valued.v (mat v g 1 0) ≤ 0 := by rwa [hd, map_zero] at hcd
      have hc : mat v g 1 0 = 0 := (Valuation.zero_iff _).mp (le_antisymm this zero_le')
      apply hdet; rw [hd, hc]; ring
    have hα : (mat v g 0 0 * mat v g 1 1 - mat v g 0 1 * mat v g 1 0) / mat v g 1 1 ≠ 0 := div_ne_zero hdet hd
    refine ⟨_, _, _, hα, hd, lowerU v (mat v g 1 0 / mat v g 1 1), lowerU_mem v ?_, decomp_d v g hd hα⟩
    rw [map_div₀]
    exact div_le_one_of_le₀ hcd zero_le'
  ·
    push_neg at hcd
    have hc : mat v g 1 0 ≠ 0 := fun h => by
      rw [h, map_zero] at hcd
      exact (not_lt_of_ge zero_le') hcd
    have hdet' : mat v g 0 1 * mat v g 1 0 - mat v g 0 0 * mat v g 1 1 ≠ 0 := fun h => hdet (by linear_combination -h)
    have hα : (mat v g 0 1 * mat v g 1 0 - mat v g 0 0 * mat v g 1 1) / mat v g 1 0 ≠ 0 := div_ne_zero hdet' hc
    refine ⟨_, _, _, hα, hc, lowerU v (mat v g 1 1 / mat v g 1 0) * wK v,
      Subgroup.mul_mem _ (lowerU_mem v ?_) (wK_mem v), decomp_c v g hc hα⟩
    rw [map_div₀]
    exact div_le_one_of_le₀ hcd.le zero_le'

variable {ϖ : Fv v} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
include hπ

def dgz (a b : ℤ) : GL (Fin 2) (Fv v) := dg v (ϖ ^ a) (ϖ ^ b) (zpow_ne_zero a hπ) (zpow_ne_zero b hπ)

theorem dgz_mul_scalarPi (a b : ℤ) : dgz v hπ a b * scalarPi ϖ hπ = dgz v hπ (a + 1) (b + 1) := by
  apply Units.ext
  change mat v (dgz v hπ a b) * mat v (scalarPi ϖ hπ) = mat v (dgz v hπ (a + 1) (b + 1))
  simp only [dgz, mat_dg, mat_scalarPi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ]

theorem dgz_zero_right (m : ℤ) : dgz v hπ m 0 = diagZ ϖ hπ m := by
  apply Units.ext
  change mat v (dgz v hπ m 0) = mat v (diagZ ϖ hπ m)
  simp only [dgz, mat_dg, mat_diagZ, zpow_zero]

include hϖ

omit hπ in
theorem v_zpow (a : ℤ) : Valued.v (ϖ ^ a) = WithZero.exp (-a) := by
  rw [map_zpow₀, hϖ]
  have hne : (WithZero.exp (-1 : ℤ)) ^ a ≠ 0 := zpow_ne_zero a WithZero.exp_ne_zero
  rw [← WithZero.exp_log hne, WithZero.log_zpow, WithZero.log_exp, smul_eq_mul, mul_neg_one]

theorem unit_factor {α : Fv v} (hα : α ≠ 0) :
    Valued.v (α / ϖ ^ (-WithZero.log (Valued.v α))) = 1 := by
  have hvα : Valued.v α ≠ 0 := (Valuation.ne_zero_iff _).mpr hα
  rw [map_div₀, v_zpow v hϖ, neg_neg, WithZero.exp_log hvα]
  exact div_self hvα

theorem dg_factor {α δ : Fv v} (hα : α ≠ 0) (hδ : δ ≠ 0) :
    ∃ (a b : ℤ) (u₁ u₂ : Fv v) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0),
      Valued.v u₁ = 1 ∧ Valued.v u₂ = 1 ∧ dg v α δ hα hδ = dgz v hπ a b * dg v u₁ u₂ hu₁ hu₂ := by
  set a : ℤ := -WithZero.log (Valued.v α)
  set b : ℤ := -WithZero.log (Valued.v δ)
  have hpa : ϖ ^ a ≠ 0 := zpow_ne_zero a hπ
  have hpb : ϖ ^ b ≠ 0 := zpow_ne_zero b hπ
  refine ⟨a, b, α / ϖ ^ a, δ / ϖ ^ b, div_ne_zero hα hpa, div_ne_zero hδ hpb, unit_factor v hπ hϖ hα,
    unit_factor v hπ hϖ hδ, ?_⟩
  apply Units.ext
  change mat v (dg v α δ hα hδ) = mat v (dgz v hπ a b) * mat v (dg v (α / ϖ ^ a) (δ / ϖ ^ b) _ _)
  simp only [dgz, mat_dg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

end SlSph

end

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (θ : v.adicCompletion ℚ → ℂ) (z : ℂ) (t : ℤ → ℂ)
    (W W' : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hWψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)), W (unipotent x * g) = θ x * W g)
    (hWK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * k) = W g)
    (hWZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = z * W g)
    (hWT : ∀ m : ℤ, W (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) = t m)
    (hW'ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)), W' (unipotent x * g) = θ x * W' g)
    (hW'K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W' (g * k) = W' g)
    (hW'Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W' (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = z * W' g)
    (hW'T : ∀ m : ℤ, W' (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) = t m) :
    W = W' := by
  have hπ' : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0 := hπ

  have hpow : ∀ a b : ℤ, W (SlSph.dgz v hπ a b) = W' (SlSph.dgz v hπ a b) := by
    by_cases hz : z = 0
    · intro a b
      have e : SlSph.dgz v hπ a b = SlSph.dgz v hπ (a - 1) (b - 1) *
          scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ := by
        rw [SlSph.dgz_mul_scalarPi, sub_add_cancel, sub_add_cancel]
      rw [e, hWZ, hW'Z, hz, zero_mul, zero_mul]
    · suffices h : ∀ (b m : ℤ), W (SlSph.dgz v hπ (m + b) b) = W' (SlSph.dgz v hπ (m + b) b) by
        intro a b
        have := h b (a - b)
        rwa [sub_add_cancel] at this
      intro b
      refine Int.induction_on b ?_ ?_ ?_
      · intro m
        rw [add_zero, SlSph.dgz_zero_right, hWT, hW'T]
      · intro i ih m
        have e : SlSph.dgz v hπ (m + ((i : ℤ) + 1)) ((i : ℤ) + 1) = SlSph.dgz v hπ (m + i) i *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ := by
          rw [SlSph.dgz_mul_scalarPi, add_assoc]
        rw [e, hWZ, hW'Z, ih m]
      · intro i ih m
        have e : SlSph.dgz v hπ (m + (-(i : ℤ) - 1)) (-(i : ℤ) - 1) *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ =
            SlSph.dgz v hπ (m + -(i : ℤ)) (-(i : ℤ)) := by
          rw [SlSph.dgz_mul_scalarPi]; congr 1 <;> ring
        have h1 := hWZ (SlSph.dgz v hπ (m + (-(i : ℤ) - 1)) (-(i : ℤ) - 1))
        have h2 := hW'Z (SlSph.dgz v hπ (m + (-(i : ℤ) - 1)) (-(i : ℤ) - 1))
        rw [e] at h1 h2
        have h3 := ih m
        rw [h1, h2] at h3
        exact mul_left_cancel₀ hz h3

  funext g
  obtain ⟨x, α, δ, hα, hδ, k, hk, hg⟩ := SlSph.iwasawa v g
  obtain ⟨a, b, u₁, u₂, hu₁, hu₂, hvu₁, hvu₂, hD⟩ := SlSph.dg_factor v hπ hϖ hα hδ
  have hkD : SlSph.dg v u₁ u₂ hu₁ hu₂ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := SlSph.dg_mem v hvu₁ hvu₂ hu₁ hu₂
  rw [hg, hD, mul_assoc, hWψ, hW'ψ, hWK k _ hk, hW'K k _ hk, hWK _ _ hkD, hW'K _ _ hkD, hpow a b]

end S_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ
end P2MW
export P2MW.S_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ (solution)
