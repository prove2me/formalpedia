-- Prove2me | solution 1 for RLCDiscrepancy.theorem_2_4_translation_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:17:39.651198+00:00
-- url     : https://prove2.me/submissions/6a49636e-fc3a-4bcb-b3d3-0aa3d59a71f7

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_transl
import Definitions.Def_RLCDiscrepancy_capacity
import Definitions.Def_RLCDiscrepancy_rlc
import Definitions.Def_RLCDiscrepancy_consSeq
import Definitions.Def_RLCDiscrepancy_IsSmooth
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_smoothLambda
import Definitions.Def_RLCDiscrepancy_l2NormSq
import Definitions.Def_PunctSketch_coinProb
import Theorems.Thm_RLCDiscrepancy_lemma_4_4
import Theorems.Thm_RLCDiscrepancy_lemma_4_11
import Theorems.Thm_RLCDiscrepancy_lemma_4_14

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace RLCDiscrepancy.Dev.T24
open RLCDiscrepancy
open scoped Classical

/-! ### Probability helpers -/

section prob
variable {Ω : Type*} [Fintype Ω]

lemma coinProb_nonneg (A : Ω → Prop) : 0 ≤ PunctSketch.coinProb A := by
  unfold PunctSketch.coinProb; positivity

lemma coinProb_biUnion_le {ι : Type*} (s : Finset ι) (Q : ι → Ω → Prop) :
    PunctSketch.coinProb (fun ω => ∃ i ∈ s, Q i ω) ≤ ∑ i ∈ s, PunctSketch.coinProb (Q i) := by
  unfold PunctSketch.coinProb
  rcases isEmpty_or_nonempty Ω with h | h
  · simp
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [← Finset.sum_div, div_le_div_iff_of_pos_right hc]
  have hsub : Finset.univ.filter (fun ω => ∃ i ∈ s, Q i ω)
      ⊆ s.biUnion (fun i => Finset.univ.filter (Q i)) := by
    intro ω hω; simpa using hω
  have h3 := (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le (s := s) (t := fun i => Finset.univ.filter (Q i)))
  have h4 := (Nat.cast_le (α := ℝ)).mpr h3
  push_cast at h4
  convert h4 using 3 <;> first | rfl | (ext; simp)

lemma coinProb_ge [Nonempty Ω] (P B C : Ω → Prop) (h : ∀ ω, ¬ P ω → B ω ∨ C ω) :
    1 - PunctSketch.coinProb B - PunctSketch.coinProb C ≤ PunctSketch.coinProb P := by
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have h1 : (Finset.univ.filter (fun ω => ¬ P ω)).card
      ≤ (Finset.univ.filter B).card + (Finset.univ.filter C).card := by
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rcases h ω hω with h | h <;> simp [h]
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω)) P
  rw [Finset.card_univ] at h2
  unfold PunctSketch.coinProb
  have h1' : ((Finset.univ.filter (fun ω => ¬ P ω)).card : ℝ)
      ≤ (Finset.univ.filter B).card + (Finset.univ.filter C).card := by exact_mod_cast h1
  have h2' : ((Finset.univ.filter P).card : ℝ) + (Finset.univ.filter (fun ω => ¬ P ω)).card
      = Fintype.card Ω := by exact_mod_cast h2
  rw [← sub_nonneg]
  have : ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω
      - (1 - ((Finset.univ.filter B).card : ℝ) / Fintype.card Ω
        - ((Finset.univ.filter C).card : ℝ) / Fintype.card Ω)
      = (((Finset.univ.filter B).card : ℝ) + (Finset.univ.filter C).card
        - (Finset.univ.filter (fun ω => ¬ P ω)).card) / Fintype.card Ω := by
    field_simp
    linarith
  rw [this]
  apply div_nonneg _ hc.le
  linarith

end prob

theorem sum_comp_surj {A B : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup B] [Fintype B]
    [DecidableEq B] (Φ : A →+ B) (hΦ : Function.Surjective Φ) (φ : B → ℝ) :
    (Fintype.card B : ℝ) * ∑ a, φ (Φ a) = Fintype.card A * ∑ b, φ b := by
  set K := Finset.card (Finset.univ.filter (fun a => Φ a = 0)) with hK
  have hfib : ∀ b, Finset.card (Finset.univ.filter (fun a => Φ a = b)) = K := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range Φ (hΦ b) (hΦ 0)
  have hcard : Fintype.card A = Fintype.card B * K := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := Φ) (t := Finset.univ) (by simp)]
    simp [hfib]
  have hsum : ∑ a, φ (Φ a) = ∑ b, (K : ℝ) * φ b := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => φ b) (fun a ha => by rw [(Finset.mem_filter.1 ha).2])]
    simp [hfib]
  rw [hsum, ← Finset.mul_sum, hcard]; push_cast; ring

lemma coinProb_comp_surj {A B : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup B] [Fintype B]
    (Φ : A →+ B) (hΦ : Function.Surjective Φ) (E : B → Prop) :
    PunctSketch.coinProb (fun a => E (Φ a)) = PunctSketch.coinProb E := by
  have h := sum_comp_surj Φ hΦ (fun b => if E b then (1 : ℝ) else 0)
  simp only [Finset.sum_boole] at h
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  unfold PunctSketch.coinProb
  rw [div_eq_div_iff hA.ne' hB.ne']
  linarith

/-! ### Codes and columns -/

section cols
variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

/-- the first `i` columns of `u`, as a matrix. -/
def Φ {k : ℕ} (i : ℕ) (h : i ≤ k) : (Fin k → Fin n → F) →+ Matrix (Fin n) (Fin i) F where
  toFun u := Matrix.of fun a j => u (Fin.castLE h j) a
  map_zero' := by ext; simp
  map_add' u v := by ext; simp

lemma Φ_surj {k : ℕ} (i : ℕ) (h : i ≤ k) : Function.Surjective (Φ (F := F) (n := n) i h) := by
  intro G
  refine ⟨fun j a => if hj : (j : ℕ) < i then G a ⟨j, hj⟩ else 0, ?_⟩
  ext a j
  simp [Φ]

lemma rlc_Φ {k : ℕ} (i : ℕ) (h : i ≤ k) (u : Fin k → Fin n → F) :
    rlc (Φ i h u) = consSeq u i := by
  unfold rlc consSeq
  rw [Matrix.range_mulVecLin]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply Submodule.subset_span
    refine ⟨Fin.castLE h j, by simp, ?_⟩
    ext a; simp [Φ, Matrix.col]
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨j, hj⟩, ?_⟩
    ext a; simp [Φ, Matrix.col]

end cols

/-! ### Facts about functions -/

section fn
variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

lemma card_fun_eq : (Fintype.card (Fin n → F) : ℝ) = (Fintype.card F : ℝ) ^ n := by
  simp [Fintype.card_fun]

lemma qpos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos

lemma q_gt_one : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card

lemma le_supNorm (f : (Fin n → F) → ℝ) (x : Fin n → F) : f x ≤ supNorm f :=
  (le_abs_self _).trans (Finset.le_sup' (fun x => |f x|) (Finset.mem_univ x))

lemma one_le_supNorm (f : (Fin n → F) → ℝ) (hf : IsNormalized f) : 1 ≤ supNorm f := by
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := pow_pos qpos n
  have h : ∑ x, f x ≤ ∑ _x : Fin n → F, supNorm f := Finset.sum_le_sum (fun x _ => le_supNorm f x)
  rw [hf.2] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [card_fun_eq] at h
  nlinarith

lemma supNorm_transl (f : (Fin n → F) → ℝ) (z : Fin n → F) :
    supNorm (transl f z) = supNorm f := by
  unfold supNorm transl
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun x _ =>
      Finset.le_sup' (fun x => |f x|) (Finset.mem_univ (x + z)))
  · refine Finset.sup'_le _ _ (fun x _ => ?_)
    have := Finset.le_sup' (fun x => |f (x + z)|) (Finset.mem_univ (x - z))
    rw [sub_add_cancel] at this
    exact this

lemma smoothLambda_transl (f : (Fin n → F) → ℝ) (z : Fin n → F) (k : ℕ) (Γ : ℝ) :
    smoothLambda (transl f z) k Γ = smoothLambda f k Γ := by
  unfold smoothLambda; rw [supNorm_transl]

lemma isNormalized_transl (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (z : Fin n → F) :
    IsNormalized (transl f z) := by
  refine ⟨fun x => hf.1 _, ?_⟩
  rw [← hf.2]
  exact Fintype.sum_equiv (Equiv.addRight z) _ _ (fun _ => rfl)

lemma isNormalized_selfConv (f : (Fin n → F) → ℝ) (hf : IsNormalized f) :
    IsNormalized (selfConv f) := by
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := pow_pos qpos n
  refine ⟨fun w => ?_, ?_⟩
  · unfold selfConv
    exact div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (hf.1 _) (hf.1 _)) hN.le
  · unfold selfConv
    rw [← Finset.sum_div, Finset.sum_comm, div_eq_iff hN.ne']
    have : ∀ x, ∑ w, f x * f (x - w) = f x * (Fintype.card F : ℝ) ^ n := by
      intro x
      rw [← Finset.mul_sum, ← hf.2]
      congr 1
      exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)
    simp only [this, ← Finset.sum_mul, hf.2]

lemma selfConv_le (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (w : Fin n → F) :
    selfConv f w ≤ supNorm f := by
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := pow_pos qpos n
  unfold selfConv
  rw [div_le_iff₀ hN]
  calc ∑ x, f x * f (x - w) ≤ ∑ x, f x * supNorm f :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (le_supNorm f _) (hf.1 x)
    _ = supNorm f * (Fintype.card F : ℝ) ^ n := by rw [← Finset.sum_mul, hf.2]; ring

lemma l2NormSq_le (g : (Fin n → F) → ℝ) (hg : IsNormalized g) (M : ℝ) (hM : ∀ x, g x ≤ M) :
    l2NormSq g ≤ M := by
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := pow_pos qpos n
  unfold l2NormSq
  rw [div_le_iff₀ hN]
  calc ∑ x, g x ^ 2 ≤ ∑ x, g x * M :=
        Finset.sum_le_sum fun x _ => by
          rw [sq]; exact mul_le_mul_of_nonneg_left (hM x) (hg.1 x)
    _ = M * (Fintype.card F : ℝ) ^ n := by rw [← Finset.sum_mul, hg.2]; ring

/-- the per-index tail bound, via Lemma 4.4 -/
lemma tail_i (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (k : ℕ) (hkn : k ≤ n) (i : ℕ)
    (hik : i ≤ k) (Γ : ℝ) (hΓ : 0 < Γ)
    (hbig : 2 * supNorm f ≤ (Fintype.card F : ℝ) ^ k * Γ) :
    PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        (Fintype.card F : ℝ) ^ (k - i) * Γ < |relDev (consSeq u i) (selfConv f)|) ≤
      4 * ((Fintype.card F : ℝ) - 1) * supNorm f * (Fintype.card F : ℝ) ^ i /
          (((Fintype.card F : ℝ) ^ k) ^ 2 * Γ ^ 2)
        + (Fintype.card F : ℝ) ^ i / ((Fintype.card F : ℝ) ^ n * ((Fintype.card F : ℝ) - 1)) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : 1 < q := q_gt_one
  have hq0 : 0 < q := by linarith
  set M := supNorm f with hM
  have hM1 : 1 ≤ M := one_le_supNorm f hf
  set g := selfConv f with hg
  have hgn : IsNormalized g := isNormalized_selfConv f hf
  have hg0 : 0 ≤ g 0 := hgn.1 0
  have hg1 : g 0 ≤ M := selfConv_le f hf 0
  have habs : |g 0 - 1| ≤ M := by rw [abs_le]; constructor <;> linarith
  have hin : i ≤ n := hik.trans hkn
  set a : ℝ := q ^ i with ha
  set b : ℝ := q ^ (k - i) with hb
  have ha0 : 0 < a := pow_pos hq0 i
  have hb0 : 0 < b := pow_pos hq0 _
  have hab : q ^ k = a * b := by
    rw [ha, hb, ← pow_add, Nat.add_sub_cancel' hik]
  have hbig' : 2 * M ≤ a * (b * Γ) := by rw [← mul_assoc, ← hab]; exact hbig
  have hD : b * Γ / 2 ≤ b * Γ - a⁻¹ * |g 0 - 1| := by
    have : a⁻¹ * |g 0 - 1| ≤ b * Γ / 2 := by
      rw [inv_mul_le_iff₀ ha0]; nlinarith
    linarith
  have hbΓ : 0 < b * Γ := mul_pos hb0 hΓ
  have hΔ : a⁻¹ * |g 0 - 1| < b * Γ := by linarith
  have h44 := lemma_4_4 (F := F) n i hin g hgn (b * Γ) hΔ
  have hE : (fun u : Fin k → Fin n → F => b * Γ < |relDev (consSeq u i) g|)
      = (fun u => (fun G : Matrix (Fin n) (Fin i) F => b * Γ < |relDev (rlc G) g|)
          (Φ i hik u)) := by
    funext u; simp only [rlc_Φ]
  have hprob : PunctSketch.coinProb (fun u : Fin k → Fin n → F => b * Γ < |relDev (consSeq u i) g|)
      = PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin i) F => b * Γ < |relDev (rlc G) g|) := by
    rw [hE]
    exact coinProb_comp_surj (A := Fin k → Fin n → F) (B := Matrix (Fin n) (Fin i) F) (Φ i hik)
      (Φ_surj i hik) (fun G : Matrix (Fin n) (Fin i) F => b * Γ < |relDev (rlc G) g|)
  rw [hprob]
  refine h44.trans ?_
  have hl2 : l2NormSq g ≤ M := l2NormSq_le g hgn M (selfConv_le f hf)
  have hl20 : 0 ≤ l2NormSq g := by
    unfold l2NormSq; exact div_nonneg (Finset.sum_nonneg fun x _ => sq_nonneg _) (pow_pos qpos n).le
  have hDpos : 0 < b * Γ - a⁻¹ * |g 0 - 1| := by linarith
  have hq1' : 0 < q - 1 := by linarith
  have hfirst : (q - 1) / (q ^ i * (b * Γ - a⁻¹ * |g 0 - 1|) ^ 2) * l2NormSq g
      ≤ 4 * (q - 1) * M * a / ((q ^ k) ^ 2 * Γ ^ 2) := by
    have h1 : (q - 1) / (q ^ i * (b * Γ - a⁻¹ * |g 0 - 1|) ^ 2)
        ≤ (q - 1) / (a * (b * Γ / 2) ^ 2) := by
      apply div_le_div_of_nonneg_left hq1'.le (by positivity)
      apply mul_le_mul_of_nonneg_left _ ha0.le
      exact pow_le_pow_left₀ (by positivity) hD 2
    calc (q - 1) / (q ^ i * (b * Γ - a⁻¹ * |g 0 - 1|) ^ 2) * l2NormSq g
        ≤ (q - 1) / (a * (b * Γ / 2) ^ 2) * M :=
          mul_le_mul h1 hl2 hl20 (by positivity)
      _ = 4 * (q - 1) * M * a / ((q ^ k) ^ 2 * Γ ^ 2) := by
          rw [hab]; field_simp; norm_num
  have hsecond : q ^ ((i : ℝ) - n) / (q - 1) = a / (q ^ n * (q - 1)) := by
    rw [Real.rpow_sub hq0, Real.rpow_natCast, Real.rpow_natCast]; field_simp; exact ha.symm
  rw [hsecond]
  exact add_le_add hfirst le_rfl

lemma geom_bound (q M Γ : ℝ) (k n : ℕ) (hq1 : 1 < q) (hΓ : 0 < Γ) (hM : 0 ≤ M) :
    ∑ i ∈ Finset.range (k + 1), (4 * (q - 1) * M * q ^ i / ((q ^ k) ^ 2 * Γ ^ 2)
      + q ^ i / (q ^ n * (q - 1))) ≤
      4 * M * q / (q ^ k * Γ ^ 2) + q ^ (k + 1) / (q ^ n * (q - 1) ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hq1' : 0 < q - 1 := by linarith
  set c1 : ℝ := 4 * (q - 1) * M / ((q ^ k) ^ 2 * Γ ^ 2) with hc1
  set c2 : ℝ := 1 / (q ^ n * (q - 1)) with hc2
  have hrw : ∀ i : ℕ, 4 * (q - 1) * M * q ^ i / ((q ^ k) ^ 2 * Γ ^ 2)
      + q ^ i / (q ^ n * (q - 1)) = (c1 + c2) * q ^ i := by
    intro i; rw [hc1, hc2]; ring
  simp only [hrw]
  rw [← Finset.mul_sum, geom_sum_eq hq1.ne']
  have hc1p : 0 ≤ c1 := by positivity
  have hc2p : 0 ≤ c2 := by positivity
  have hgeo : (q ^ (k + 1) - 1) / (q - 1) ≤ q ^ (k + 1) / (q - 1) :=
    div_le_div_of_nonneg_right (by linarith) hq1'.le
  calc (c1 + c2) * ((q ^ (k + 1) - 1) / (q - 1)) ≤ (c1 + c2) * (q ^ (k + 1) / (q - 1)) :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 4 * M * q / (q ^ k * Γ ^ 2) + q ^ (k + 1) / (q ^ n * (q - 1) ^ 2) := by
        rw [hc1, hc2, pow_succ]
        have : 0 < q ^ k := pow_pos hq0 k
        field_simp
        ring

/-- the event that the self-convolution sequence is not smooth. -/
lemma tail_A (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (k : ℕ) (hkn : k ≤ n) (Γ : ℝ)
    (hΓ : 0 < Γ) (hbig : 2 * supNorm f ≤ (Fintype.card F : ℝ) ^ k * Γ) :
    PunctSketch.coinProb (fun u : Fin k → Fin n → F => ¬ IsSmooth u (selfConv f) Γ k) ≤
      4 * supNorm f * (Fintype.card F : ℝ) / ((Fintype.card F : ℝ) ^ k * Γ ^ 2)
        + (Fintype.card F : ℝ) ^ (k + 1) /
            ((Fintype.card F : ℝ) ^ n * ((Fintype.card F : ℝ) - 1) ^ 2) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : 1 < q := q_gt_one
  have hq0 : 0 < q := by linarith
  have hev : (fun u : Fin k → Fin n → F => ¬ IsSmooth u (selfConv f) Γ k)
      = fun u => ∃ i ∈ Finset.range (k + 1),
          q ^ (k - i) * Γ < |relDev (consSeq u i) (selfConv f)| := by
    funext u
    simp only [IsSmooth, not_forall, not_le, eq_iff_iff]
    constructor
    · rintro ⟨i, hi, h⟩; exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), h⟩
    · rintro ⟨i, hi, h⟩; exact ⟨i, Nat.le_of_lt_succ (Finset.mem_range.mp hi), h⟩
  rw [hev]
  refine (coinProb_biUnion_le _ _).trans ?_
  have hterm := fun i (hi : i ∈ Finset.range (k + 1)) =>
    tail_i f hf k hkn i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) Γ hΓ hbig
  refine (Finset.sum_le_sum hterm).trans ?_
  exact geom_bound _ _ _ k n hq1 hΓ (by linarith [one_le_supNorm f hf])

/-- the union over translations of Lemma 4.14 -/
lemma bad_z (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (k : ℕ) (hkn : k ≤ n) (Γ : ℝ)
    (hΓ : 0 < Γ) (t : ℝ) (ht : 20 * Real.logb (Fintype.card F) n ≤ t) (htk : t ≤ k) :
    PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧ ∃ z : Fin n → F,
          ¬ IsSmooth u (transl f z) ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) ≤
      (Fintype.card F : ℝ) ^ n * ((Fintype.card F : ℝ) ^ n *
        (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2)) := by
  have hev : (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧ ∃ z : Fin n → F,
          ¬ IsSmooth u (transl f z) ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k)
      = fun u => ∃ z ∈ (Finset.univ : Finset (Fin n → F)),
          (IsSmooth u (selfConv f) Γ k ∧
          ¬ IsSmooth u (transl f z) ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) := by
    funext u; simp only [Finset.mem_univ, true_and, eq_iff_iff]
    constructor
    · rintro ⟨h1, z, h2⟩; exact ⟨z, h1, h2⟩
    · rintro ⟨z, h1, h2⟩; exact ⟨h1, z, h2⟩
  rw [hev]
  refine (coinProb_biUnion_le _ _).trans ?_
  have hz : ∀ z ∈ (Finset.univ : Finset (Fin n → F)),
      PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
          IsSmooth u (selfConv f) Γ k ∧
          ¬ IsSmooth u (transl f z) ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) ≤
        (Fintype.card F : ℝ) ^ n * (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) := by
    intro z _
    have h := lemma_4_14 (F := F) n k hkn (transl f z) (isNormalized_transl f hf z) Γ hΓ t ht htk
    simp only [lemma_4_11, smoothLambda_transl] at h
    exact h
  refine (Finset.sum_le_sum hz).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_fun_eq]

end fn

end RLCDiscrepancy.Dev.T24

namespace RLCDiscrepancy
open RLCDiscrepancy.Dev.T24 in
theorem chk_theorem_2_4_translation_family {F : Type*} [Field F] [Fintype F] (n k : ℕ)
    (hkn : k ≤ n) (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (η : ℝ) (hη : 0 < η)
    (hk : (k : ℝ) = (capacity f + η) * n)
    (hn : 240 * Real.logb (Fintype.card F) n ≤ η * n) :
    1 - 4 * (Fintype.card F : ℝ) ^ (1 - η * n / 3)
        - (Fintype.card F : ℝ) ^ ((k : ℝ) - n + 1) / ((Fintype.card F : ℝ) - 1) ^ 2
        - (Fintype.card F : ℝ) ^ (2 * (n : ℝ) - η ^ 2 * n ^ 2 / 1440) ≤
      PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin k) F =>
        ∀ z : Fin n → F, |relDev (rlc G) (transl f z)| ≤
          (Fintype.card F : ℝ) ^ (-(η / 12) * n)) := by
  have hq1 : (1 : ℝ) < Fintype.card F := q_gt_one
  have hq0 : (0 : ℝ) < Fintype.card F := qpos
  have hq2 : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  set q : ℝ := (Fintype.card F : ℝ) with hq
  by_cases hLHS : 1 - 4 * q ^ (1 - η * n / 3) - q ^ ((k : ℝ) - n + 1) / (q - 1) ^ 2
      - q ^ (2 * (n : ℝ) - η ^ 2 * n ^ 2 / 1440) ≤ 0
  · exact hLHS.trans (coinProb_nonneg _)
  push Not at hLHS
  have hc2 : 0 ≤ q ^ ((k : ℝ) - n + 1) / (q - 1) ^ 2 := by positivity
  have hc3 : 0 ≤ q ^ (2 * (n : ℝ) - η ^ 2 * n ^ 2 / 1440) := by positivity
  have h4 : 4 * q ^ (1 - η * n / 3) < 1 := by linarith
  set e : ℝ := η * n with he
  -- e > 0
  have he0 : 0 < e := by
    by_contra hle
    push Not at hle
    have : q ^ (1 : ℝ) ≤ q ^ (1 - e / 3) :=
      Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
    rw [Real.rpow_one] at this
    linarith
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso; rw [he, h] at he0; simp at he0
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set Y : ℝ := q ^ (e / 12) with hY
  have hYpow : ∀ m : ℕ, Y ^ m = q ^ (e / 12 * m) := by
    intro m; rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
  have hY1 : 1 < Y := Real.one_lt_rpow hq1 (by linarith)
  have hY0 : 0 < Y := by linarith
  have hexp : ∀ m : ℕ, ∀ c : ℝ, e / 12 * (m : ℝ) = c → Y ^ m = q ^ c := by
    intro m c h; rw [hYpow, h]
  have h1e : q ^ (1 - e / 3) = q * (Y ^ 4)⁻¹ := by
    rw [Real.rpow_sub hq0, Real.rpow_one, hexp 4 (e / 3) (by push_cast; ring), div_eq_mul_inv]
  have hY4 : 4 * q < Y ^ 4 := by
    have hp : 0 < Y ^ 4 := by positivity
    rw [h1e] at h4
    have : 4 * q * (Y ^ 4)⁻¹ < 1 := by linarith
    rw [← div_eq_mul_inv, div_lt_one hp] at this
    exact this
  have hY48 : 8 ≤ Y ^ 4 := by linarith
  -- the supremum norm
  set M : ℝ := supNorm f with hM
  have hM1 : 1 ≤ M := one_le_supNorm f hf
  have hM0 : 0 < M := by linarith
  set L : ℝ := Real.logb q M with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg hq1 hM1
  have hML : M = q ^ L := (Real.rpow_logb hq0 hq1.ne' hM0).symm
  have hcap : capacity f * n = L := by
    unfold capacity; rw [div_mul_cancel₀ _ hnR.ne']
  have hkL : (k : ℝ) = L + e := by rw [hk, add_mul, hcap]
  have hqk : q ^ k = M * Y ^ 12 := by
    rw [← Real.rpow_natCast, hkL, Real.rpow_add hq0, ← hML, hexp 12 e (by push_cast; ring)]
  set Γ : ℝ := (Y ^ 4)⁻¹ with hΓ
  have hΓ0 : 0 < Γ := by positivity
  have hbig : 2 * M ≤ q ^ k * Γ := by
    have : q ^ k * Γ = M * Y ^ 8 := by
      rw [hqk, hΓ]; field_simp
    rw [this]
    have : 2 ≤ Y ^ 8 := by nlinarith [pow_pos hY0 4]
    nlinarith
  have hA := tail_A f hf k hkn Γ hΓ0 hbig
  rw [← hq, ← hM] at hA
  have hA1 : 4 * M * q / (q ^ k * Γ ^ 2) = 4 * q ^ (1 - e / 3) := by
    rw [h1e, hqk, hΓ]; field_simp
  have hA2 : q ^ (k + 1) / (q ^ n * (q - 1) ^ 2) = q ^ ((k : ℝ) - n + 1) / (q - 1) ^ 2 := by
    rw [Real.rpow_add hq0, Real.rpow_sub hq0, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_one,
      pow_succ]
    field_simp
  rw [hA1, hA2] at hA
  -- the translation part
  set t : ℝ := e / 12 with ht
  have htY : q ^ t = Y := rfl
  have ht1 : 20 * Real.logb q n ≤ t := by rw [ht]; linarith
  have htk : t ≤ k := by rw [hkL, ht]; linarith
  have hB := bad_z f hf k hkn Γ hΓ0 t ht1 htk
  rw [← hq] at hB
  have hB1 : q ^ n * (q ^ n * q ^ (-(1 / 10 : ℝ) * t ^ 2))
      = q ^ (2 * (n : ℝ) - η ^ 2 * n ^ 2 / 1440) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hq0, ← Real.rpow_natCast, ← Real.rpow_add hq0]
    congr 1
    have htn : t = η * n / 12 := by rw [ht, he]
    rw [htn, Real.rpow_natCast]
    ring
  rw [hB1] at hB
  -- the bound on Γ'
  have hsl : smoothLambda f k Γ ≤ (Y ^ 2)⁻¹ := by
    unfold smoothLambda
    rw [← hM, ← hq]
    apply max_le
    · rw [hqk]
      have : M * (M * Y ^ 12)⁻¹ = (Y ^ 12)⁻¹ := by field_simp
      rw [this]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hY1.le (by norm_num))
    · have : Γ = ((Y ^ 2)⁻¹) ^ 2 := by rw [hΓ]; field_simp
      rw [this, Real.sqrt_sq (by positivity)]
  have hΓ' : q ^ t * smoothLambda f k Γ ≤ q ^ (-(η / 12) * n) := by
    have hsm0 : 0 ≤ smoothLambda f k Γ := le_max_of_le_left (by positivity)
    have : -(η / 12) * n = -t := by rw [ht, he]; ring
    rw [this, Real.rpow_neg hq0.le, htY]
    calc Y * smoothLambda f k Γ ≤ Y * (Y ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hsl hY0.le
      _ = Y⁻¹ := by field_simp
  -- assemble
  have hP : PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin k) F =>
        ∀ z : Fin n → F, |relDev (rlc G) (transl f z)| ≤ q ^ (-(η / 12) * n))
      = PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        ∀ z : Fin n → F, |relDev (consSeq u k) (transl f z)| ≤ q ^ (-(η / 12) * n)) := by
    have := coinProb_comp_surj (A := Fin k → Fin n → F) (B := Matrix (Fin n) (Fin k) F)
      (Φ k le_rfl) (Φ_surj k le_rfl) (fun G : Matrix (Fin n) (Fin k) F =>
        ∀ z : Fin n → F, |relDev (rlc G) (transl f z)| ≤ q ^ (-(η / 12) * n))
    rw [← this]
    simp only [rlc_Φ]
  rw [hP]
  have hge := coinProb_ge (Ω := Fin k → Fin n → F)
    (fun u => ∀ z : Fin n → F, |relDev (consSeq u k) (transl f z)| ≤ q ^ (-(η / 12) * n))
    (fun u => ¬ IsSmooth u (selfConv f) Γ k)
    (fun u => IsSmooth u (selfConv f) Γ k ∧ ∃ z : Fin n → F,
          ¬ IsSmooth u (transl f z) (q ^ t * smoothLambda f k Γ) k) (by
      intro u hu
      by_cases hs : IsSmooth u (selfConv f) Γ k
      · right
        refine ⟨hs, ?_⟩
        by_contra hne
        push Not at hne
        apply hu
        intro z
        have := hne z k le_rfl
        simp only [Nat.sub_self, pow_zero, one_mul] at this
        exact this.trans hΓ'
      · left; exact hs)
  linarith

end RLCDiscrepancy
end

theorem solution : type_of% @RLCDiscrepancy.chk_theorem_2_4_translation_family := @RLCDiscrepancy.chk_theorem_2_4_translation_family
