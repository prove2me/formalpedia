-- Prove2me | solution 1 for OnlineStochMatching.SuggestedMatching.opt_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:12:02.345659+00:00
-- url     : https://prove2.me/submissions/aaf6bd8a-4c72-421d-83e5-300a45458524

import Mathlib
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Cut
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

open Classical

namespace OnlineStochMatching.SuggestedMatching

section mcd
open MeasureTheory ProbabilityTheory

lemma hoeffding_fin {S : Type} [Fintype S] [Nonempty S] (g : S → ℝ) (a c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ s, a ≤ g s ∧ g s ≤ a + c) (t : ℝ) :
    (∑ s, Real.exp (t * (g s - (∑ s, g s) / Fintype.card S))) / Fintype.card S
      ≤ Real.exp (t^2 * c^2 / 8) := by
  letI : MeasurableSpace S := ⊤
  haveI : MeasurableSingletonClass S := ⟨fun _ => trivial⟩
  let μ : Measure S := (PMF.uniformOfFintype S).toMeasure
  haveI : IsProbabilityMeasure μ := PMF.toMeasure.isProbabilityMeasure _
  have hm : AEMeasurable g μ := (measurable_of_finite g).aemeasurable
  have hb : ∀ᵐ s ∂μ, g s ∈ Set.Icc a (a+c) := Filter.Eventually.of_forall (fun s => hg s)
  have h1 := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb).mgf_le t
  have hN : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hint : ∀ f : S → ℝ, ∫ s, f s ∂μ = (∑ s, f s) / Fintype.card S := by
    intro f
    rw [PMF.integral_eq_sum]
    simp [PMF.uniformOfFintype_apply, tsum_fintype, Finset.sum_div, div_eq_inv_mul, Finset.mul_sum]
  have h2 : mgf (fun s => g s - μ[g]) μ t = (∑ s, Real.exp (t * (g s - (∑ s, g s) / Fintype.card S))) / Fintype.card S := by
    unfold mgf
    rw [hint]
    have : μ[g] = (∑ s, g s) / Fintype.card S := hint g
    rw [this]
  rw [← h2]
  refine h1.trans (le_of_eq ?_)
  congr 1
  have : ‖(a + c) - a‖₊ = c.toNNReal := by
    apply NNReal.eq; simp [abs_of_nonneg hc, Real.coe_toNNReal c hc]
  rw [this]
  rw [NNReal.coe_pow, NNReal.coe_div, Real.coe_toNNReal c hc]
  push_cast
  ring


noncomputable def avg {S : Type} [Fintype S] (f : S → ℝ) : ℝ := (∑ s, f s) / Fintype.card S

lemma sum_cons {Ω : Type} [Fintype Ω] (m : ℕ) (F : (Fin (m+1) → Ω) → ℝ) :
    ∑ x, F x = ∑ x' : Fin m → Ω, ∑ ω0 : Ω, F (Fin.cons ω0 x') := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Ω)).sum_comp, Fintype.sum_prod_type_right]
  rfl

lemma avg_cons {Ω : Type} [Fintype Ω] [Nonempty Ω] (m : ℕ) (F : (Fin (m+1) → Ω) → ℝ) :
    avg F = avg (fun x' : Fin m → Ω => avg (fun ω0 : Ω => F (Fin.cons ω0 x'))) := by
  unfold avg
  rw [sum_cons]
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  simp only [Fintype.card_fun, Fintype.card_fin, pow_succ]
  rw [← Finset.sum_div]
  push_cast
  field_simp

lemma avg_mono {S : Type} [Fintype S] {f g : S → ℝ} (h : ∀ s, f s ≤ g s) : avg f ≤ avg g := by
  unfold avg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun s _ => h s)) (Nat.cast_nonneg _)

lemma avg_mul_const {S : Type} [Fintype S] (f : S → ℝ) (K : ℝ) :
    avg (fun s => f s * K) = avg f * K := by
  unfold avg
  rw [← Finset.sum_mul]; ring

lemma avg_const_mul {S : Type} [Fintype S] (f : S → ℝ) (K : ℝ) :
    avg (fun s => K * f s) = K * avg f := by
  unfold avg
  rw [← Finset.mul_sum]; ring

lemma avg_const {S : Type} [Fintype S] [Nonempty S] (K : ℝ) : avg (fun _ : S => K) = K := by
  unfold avg
  have : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  simp

def DiffOne {Ω : Type} {m : ℕ} (x y : Fin m → Ω) : Prop := ∃ i, ∀ j, j ≠ i → x j = y j

lemma diffOne_cons_zero {Ω : Type} {m : ℕ} (s r : Ω) (x : Fin m → Ω) :
    DiffOne (Fin.cons s x : Fin (m+1) → Ω) (Fin.cons r x) := by
  refine ⟨0, fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
  simp

lemma diffOne_cons_succ {Ω : Type} {m : ℕ} (s : Ω) (x y : Fin m → Ω) (h : DiffOne x y) :
    DiffOne (Fin.cons s x : Fin (m+1) → Ω) (Fin.cons s y) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i.succ, fun j hj => ?_⟩
  induction j using Fin.cases with
  | zero => simp
  | succ k =>
    have : k ≠ i := fun h => hj (by rw [h])
    simpa using hi k this

lemma mcd_mgf {Ω : Type} [Fintype Ω] [Nonempty Ω] (c : ℝ) (hc : 0 ≤ c) :
    ∀ (m : ℕ) (f : (Fin m → Ω) → ℝ),
      (∀ x y, DiffOne x y → |f x - f y| ≤ c) →
      ∀ t : ℝ, avg (fun x => Real.exp (t * (f x - avg f))) ≤ Real.exp (m * (t^2 * c^2 / 8)) := by
  intro m
  induction m with
  | zero =>
    intro f hf t
    have h0 : ∀ x : Fin 0 → Ω, f x - avg f = 0 := by
      intro x
      have hx : x = default := Subsingleton.elim _ _
      simp [avg, Finset.univ_unique, hx]
    simp only [h0, mul_zero, Real.exp_zero]
    rw [avg_const]
    simp
  | succ m ih =>
    intro f hf t
    set g : (Fin m → Ω) → ℝ := fun x' => avg (fun ω0 : Ω => f (Fin.cons ω0 x')) with hg
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hgd : ∀ x y, DiffOne x y → |g x - g y| ≤ c := by
      intro x y hxy
      have h1 : g x - g y = (∑ ω0 : Ω, (f (Fin.cons ω0 x) - f (Fin.cons ω0 y))) / Fintype.card Ω := by
        simp only [hg, avg, Finset.sum_sub_distrib, sub_div]
      rw [h1, abs_div, abs_of_pos hN, div_le_iff₀ hN]
      calc |∑ ω0 : Ω, (f (Fin.cons ω0 x) - f (Fin.cons ω0 y))|
          ≤ ∑ ω0 : Ω, |f (Fin.cons ω0 x) - f (Fin.cons ω0 y)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ ω0 : Ω, c := Finset.sum_le_sum (fun ω0 _ => hf _ _ (diffOne_cons_succ ω0 x y hxy))
        _ = c * Fintype.card Ω := by simp [mul_comm]
    have havg : avg f = avg g := avg_cons m f
    have hinner : ∀ x', avg (fun ω0 : Ω => Real.exp (t * (f (Fin.cons ω0 x') - g x')))
        ≤ Real.exp (t^2 * c^2 / 8) := by
      intro x'
      obtain ⟨w, _, hw⟩ := Finset.exists_min_image Finset.univ
        (fun ω0 : Ω => f (Fin.cons ω0 x')) Finset.univ_nonempty
      have := hoeffding_fin (fun ω0 : Ω => f (Fin.cons ω0 x')) (f (Fin.cons w x')) c hc
        (fun s => ⟨hw s (Finset.mem_univ _), by
          have := hf _ _ (diffOne_cons_zero s w x')
          have := (abs_le.mp this).2
          linarith⟩) t
      exact this
    have hdec : avg (fun x => Real.exp (t * (f x - avg f))) =
        avg (fun x' => avg (fun ω0 : Ω => Real.exp (t * (f (Fin.cons ω0 x') - g x'))) *
          Real.exp (t * (g x' - avg g))) := by
      rw [avg_cons]
      congr 1
      ext x'
      rw [← avg_mul_const]
      congr 1
      ext ω0
      rw [← Real.exp_add, havg]
      congr 1
      ring
    rw [hdec]
    calc avg (fun x' => avg (fun ω0 : Ω => Real.exp (t * (f (Fin.cons ω0 x') - g x'))) *
          Real.exp (t * (g x' - avg g)))
        ≤ avg (fun x' => Real.exp (t^2 * c^2 / 8) * Real.exp (t * (g x' - avg g))) :=
          avg_mono (fun x' => mul_le_mul_of_nonneg_right (hinner x') (Real.exp_pos _).le)
      _ = Real.exp (t^2 * c^2 / 8) * avg (fun x' => Real.exp (t * (g x' - avg g))) :=
          avg_const_mul _ _
      _ ≤ Real.exp (t^2 * c^2 / 8) * Real.exp (m * (t^2 * c^2 / 8)) :=
          mul_le_mul_of_nonneg_left (ih g hgd t) (Real.exp_pos _).le
      _ = Real.exp (((m + 1 : ℕ) : ℝ) * (t^2 * c^2 / 8)) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

lemma mcd_tail {Ω : Type} [Fintype Ω] [Nonempty Ω] (m : ℕ) (hm : 0 < m)
    (f : (Fin m → Ω) → ℝ) (hf : ∀ x y, DiffOne x y → |f x - f y| ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    ((Finset.univ.filter fun x => s ≤ f x - avg f).card : ℝ) / Fintype.card (Fin m → Ω)
      ≤ Real.exp (-2 * s^2 / m) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hC : (0 : ℝ) < Fintype.card (Fin m → Ω) := by exact_mod_cast Fintype.card_pos
  set lam : ℝ := 4 * s / m with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have h1 := mcd_mgf (Ω := Ω) 1 zero_le_one m f (by simpa using hf) lam
  have h2 : ((Finset.univ.filter fun x => s ≤ f x - avg f).card : ℝ) * Real.exp (lam * s)
      ≤ ∑ x, Real.exp (lam * (f x - avg f)) := by
    calc ((Finset.univ.filter fun x => s ≤ f x - avg f).card : ℝ) * Real.exp (lam * s)
        = ∑ x ∈ Finset.univ.filter (fun x => s ≤ f x - avg f), Real.exp (lam * s) := by
          simp [Finset.sum_const]
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x => s ≤ f x - avg f), Real.exp (lam * (f x - avg f)) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_filter] at hx
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hlam0)
      _ ≤ ∑ x, Real.exp (lam * (f x - avg f)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have h3 : ∑ x, Real.exp (lam * (f x - avg f)) ≤ Fintype.card (Fin m → Ω) * Real.exp (m * (lam^2 * 1^2 / 8)) := by
    have : avg (fun x => Real.exp (lam * (f x - avg f))) = (∑ x, Real.exp (lam * (f x - avg f))) / Fintype.card (Fin m → Ω) := rfl
    rw [this, div_le_iff₀ hC] at h1
    linarith
  have h4 : m * (lam^2 * 1^2 / 8) - lam * s = -2 * s^2 / m := by
    rw [hlam]; field_simp; ring
  rw [div_le_iff₀ hC]
  have h5 : Real.exp (-2 * s^2 / m) * Real.exp (lam * s) = Real.exp (m * (lam^2 * 1^2 / 8)) := by
    rw [← Real.exp_add, ← h4]; congr 1; ring
  have h6 : ((Finset.univ.filter fun x => s ≤ f x - avg f).card : ℝ) * Real.exp (lam * s)
      ≤ Real.exp (-2 * s^2 / m) * Fintype.card (Fin m → Ω) * Real.exp (lam * s) := by
    calc _ ≤ _ := h2.trans h3
      _ = _ := by rw [mul_assoc, mul_comm (Real.exp (-2 * s^2 / m)), mul_assoc, ← h5]; ring
  exact le_of_mul_le_mul_right h6 (Real.exp_pos _)

lemma avg_neg {S : Type} [Fintype S] (f : S → ℝ) : avg (fun s => - f s) = - avg f := by
  unfold avg; rw [Finset.sum_neg_distrib, neg_div]

lemma mcd_tail_lower {Ω : Type} [Fintype Ω] [Nonempty Ω] (m : ℕ) (hm : 0 < m)
    (f : (Fin m → Ω) → ℝ) (hf : ∀ x y, DiffOne x y → |f x - f y| ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    ((Finset.univ.filter fun x => f x - avg f ≤ -s).card : ℝ) / Fintype.card (Fin m → Ω)
      ≤ Real.exp (-2 * s^2 / m) := by
  classical
  have := mcd_tail m hm (fun x => - f x) (fun x y h => by
    have := hf x y h
    have e : -f x - -f y = -(f x - f y) := by ring
    rw [e, abs_neg]; exact this) s hs
  rw [avg_neg] at this
  convert this using 4
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h <;> linarith

end mcd


noncomputable def occ {Ω : Type} [Fintype Ω] (n : ℕ) (B : Finset Ω) (ω : Fin n → Ω) : ℕ :=
  (B.filter fun b => ∃ t, ω t = b).card

lemma card_miss {Ω : Type} [Fintype Ω] (n : ℕ) (b : Ω) :
    (Finset.univ.filter fun ω : Fin n → Ω => ∀ t, ω t ≠ b).card = (Fintype.card Ω - 1)^n := by
  have h1 : (Finset.univ.filter fun ω : Fin n → Ω => ∀ t, ω t ≠ b).card
      = Fintype.card {ω : Fin n → Ω // ∀ t, ω t ≠ b} := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ x => x ≠ b))]
  simp [Fintype.card_pi]

lemma card_hit {Ω : Type} [Fintype Ω] (n : ℕ) (b : Ω) :
    (Finset.univ.filter fun ω : Fin n → Ω => ∃ t, ω t = b).card
      = Fintype.card Ω ^ n - (Fintype.card Ω - 1)^n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Ω)))
    (fun ω : Fin n → Ω => ∃ t, ω t = b)
  have h2 := card_miss n b
  simp only [not_exists] at h
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  have : (Finset.univ.filter fun ω : Fin n → Ω => ∀ t, ¬ ω t = b) =
     (Finset.univ.filter fun ω : Fin n → Ω => ∀ t, ω t ≠ b) := rfl
  rw [this, h2] at h
  omega

lemma sum_occ {Ω : Type} [Fintype Ω] (n : ℕ) (B : Finset Ω) :
    ∑ ω : Fin n → Ω, occ n B ω = B.card * (Fintype.card Ω ^ n - (Fintype.card Ω - 1)^n) := by
  unfold occ
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ b ∈ B, ∑ ω : Fin n → Ω, (if ∃ t, ω t = b then 1 else 0)
      = Fintype.card Ω ^ n - (Fintype.card Ω - 1)^n := by
    intro b _
    rw [← card_hit n b, Finset.card_filter]
  rw [Finset.sum_congr rfl this]
  simp


variable {A I : Type} [Fintype A] [Fintype I]

noncomputable def labB (inst : Instance A I) (label : inst.Copy → Option A) : Finset inst.Copy :=
  Finset.univ.filter fun c => (label c).isSome

lemma algorithm_eq_occ (inst : Instance A I) (label : inst.Copy → Option A)
    (hl : ∀ c d a, label c = some a → label d = some a → c = d)
    (ω : Fin inst.n → inst.Copy) :
    algorithm inst label ω = occ inst.n (labB inst label) ω := by
  unfold algorithm occ labB
  set T := (Finset.univ.filter (fun c : inst.Copy => (label c).isSome)).filter
    (fun b => ∃ t, ω t = b) with hT
  set S := Finset.univ.filter fun a : A => ∃ t, label (ω t) = some a with hS
  have h1 : T.card = (T.image label).card := by
    symm
    apply Finset.card_image_of_injOn
    intro c hc d hd hcd
    have hc' : c ∈ T := hc
    rw [hT, Finset.mem_filter, Finset.mem_filter] at hc'
    obtain ⟨⟨_, hc1⟩, _⟩ := hc'
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hc1
    exact hl c d a ha (hcd ▸ ha)
  have h2 : T.image label = S.image some := by
    ext x
    simp only [hT, hS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, ⟨hc1, t, ht⟩, rfl⟩
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hc1
      exact ⟨a, ⟨t, by rw [ht]; exact ha⟩, ha.symm⟩
    · rintro ⟨a, ⟨t, ht⟩, rfl⟩
      exact ⟨ω t, ⟨by rw [ht]; rfl, t, rfl⟩, ht⟩
  have key : T.card = S.card := by
    rw [h1, h2, Finset.card_image_of_injective _ (Option.some_injective A)]
  convert key.symm


lemma card_copy (inst : Instance A I) : Fintype.card inst.Copy = inst.n := by
  simp [Instance.Copy, Fintype.card_sigma, inst.n_eq]

lemma labB_card (inst : Instance A I) (M : Finset (A × I)) (label : inst.Copy → Option A)
    (hl : IsLabelling inst M label) :
    (labB inst label).card = (coveredAds M).card := by
  obtain ⟨h1, h2⟩ := hl
  have e1 : (labB inst label).card = ((labB inst label).image label).card := by
    symm
    apply Finset.card_image_of_injOn
    intro c hc d hd hcd
    have hc' : c ∈ labB inst label := hc
    unfold labB at hc'
    rw [Finset.mem_filter] at hc'
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hc'.2
    exact h2 c d a ha (hcd ▸ ha)
  have e2 : (labB inst label).image label = (coveredAds M).image some := by
    ext x
    simp only [labB, coveredAds, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hc
      refine ⟨a, ⟨c.1, ?_⟩, ha.symm⟩
      rw [h1]
      exact ⟨c.2, by rw [← ha]⟩
    · rintro ⟨a, ⟨i, hi⟩, rfl⟩
      rw [h1] at hi
      obtain ⟨j, hj⟩ := hi
      exact ⟨⟨i, j⟩, by rw [hj]; rfl, hj⟩
  rw [e1, e2, Finset.card_image_of_injective _ (Option.some_injective A)]

lemma expect_occ {Ω : Type} [Fintype Ω] [Nonempty Ω] (n : ℕ) (B : Finset Ω) :
    (∑ ω : Fin n → Ω, (occ n B ω : ℝ)) / (Fintype.card (Fin n → Ω) : ℝ)
      = B.card * (1 - (1 - 1 / (Fintype.card Ω : ℝ)) ^ n) := by
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hs := sum_occ n B
  have hle : (Fintype.card Ω - 1)^n ≤ Fintype.card Ω ^ n := Nat.pow_le_pow_left (Nat.sub_le _ _) n
  have : (∑ ω : Fin n → Ω, (occ n B ω : ℝ)) = ((∑ ω : Fin n → Ω, occ n B ω : ℕ) : ℝ) := by push_cast; rfl
  rw [this, hs, Fintype.card_fun, Fintype.card_fin]
  have hc : ((Fintype.card Ω - 1 : ℕ) : ℝ) = (Fintype.card Ω : ℝ) - 1 := by
    rw [Nat.cast_sub Fintype.card_pos]; simp
  push_cast [Nat.cast_sub hle, hc]
  field_simp
  rw [div_pow]
  field_simp


lemma optimum_complete (n : ℕ) (hn : 0 < n)
    (ω : Fin (completeInstance n hn).n → (completeInstance n hn).Copy) :
    optimum (completeInstance n hn) ω = n := by
  unfold optimum
  apply le_antisymm
  · apply Finset.sup_le
    intro R _
    split_ifs with h
    · obtain ⟨_, _, h3⟩ := h
      have : R.card ≤ (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.2)
        · intro p _; simp [completeInstance]
        · intro p hp q hq hpq
          have hp' : p ∈ R.filter (fun x => x.2 = p.2) := Finset.mem_filter.mpr ⟨hp, rfl⟩
          have hq' : q ∈ R.filter (fun x => x.2 = p.2) := Finset.mem_filter.mpr ⟨hq, hpq.symm⟩
          exact Finset.card_le_one.mp (h3 p.2) p hp' q hq'
      simpa [completeInstance] using this
    · exact Nat.zero_le _
  · obtain ⟨R0, hR, hc⟩ : ∃ R0 : Finset (Fin n × Fin (completeInstance n hn).n),
        IsRealizationMatching (completeInstance n hn) ω R0 ∧ R0.card = n := by
      refine ⟨Finset.univ.image (fun t : Fin n => ((t, t) : Fin n × Fin (completeInstance n hn).n)), ?_, ?_⟩
      · unfold IsRealizationMatching
        refine ⟨?_, ?_, ?_⟩
        · intro p _; simp [completeInstance]
        · intro a
          apply Finset.card_le_one.mpr
          intro p hp q hq
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
          obtain ⟨⟨t, rfl⟩, h1⟩ := hp
          obtain ⟨⟨s, rfl⟩, h2⟩ := hq
          simp at h1 h2
          have : t = s := h1.trans h2.symm
          subst this; rfl
        · intro t
          apply Finset.card_le_one.mpr
          intro p hp q hq
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
          obtain ⟨⟨t1, rfl⟩, h1⟩ := hp
          obtain ⟨⟨s, rfl⟩, h2⟩ := hq
          simp at h1 h2
          have : t1 = s := h1.trans h2.symm
          subst this; rfl
      · exact (Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)).trans (by simp)
    have := Finset.le_sup (f := fun R : Finset (Fin n × Fin (completeInstance n hn).n) =>
      if IsRealizationMatching (completeInstance n hn) ω R then R.card else 0)
      (Finset.mem_univ R0)
    beta_reduce at this
    rw [if_pos hR] at this
    omega


lemma expectedAlgorithm_eq (inst : Instance A I) (M : Finset (A × I)) (label : inst.Copy → Option A)
    (hl : IsLabelling inst M label) :
    expectedAlgorithm inst label =
      (coveredAds M).card * (1 - (1 - 1 / (inst.n : ℝ)) ^ inst.n) := by
  haveI : Nonempty inst.Copy := by
    rw [← Fintype.card_pos_iff, card_copy]; exact inst.n_pos
  unfold expectedAlgorithm uniformExpectation
  have : ∀ ω : Fin inst.n → inst.Copy, (algorithm inst label ω : ℝ) = (occ inst.n (labB inst label) ω : ℝ) := by
    intro ω; rw [algorithm_eq_occ inst label hl.2 ω]
  simp only [this]
  rw [expect_occ, labB_card inst M label hl, card_copy]

lemma tightness_core (n : ℕ) (hn : 0 < n) (M : Finset (Fin n × Fin n))
    (hM : IsMaxBMatching (completeInstance n hn) M)
    (label : (completeInstance n hn).Copy → Option (Fin n))
    (hlabel : IsLabelling (completeInstance n hn) M label) :
    (∀ ω : Fin (completeInstance n hn).n → (completeInstance n hn).Copy,
      optimum (completeInstance n hn) ω = n) ∧
      expectedAlgorithm (completeInstance n hn) label =
        (n : ℝ) * (1 - (1 - 1 / (n : ℝ)) ^ n) := by
  refine ⟨optimum_complete n hn, ?_⟩
  rw [expectedAlgorithm_eq _ M label hlabel]
  have hcov : (coveredAds M).card = n := by
    apply le_antisymm
    · calc (coveredAds M).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := by simp
    · have hid : IsBMatching (completeInstance n hn) (Finset.univ.image (fun a : Fin n => (a, a))) := by
        unfold IsBMatching
        refine ⟨?_, ?_, ?_⟩
        · intro p _; simp [completeInstance]
        · intro a
          apply Finset.card_le_one.mpr
          intro p hp q hq
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
          obtain ⟨⟨t, rfl⟩, h1⟩ := hp
          obtain ⟨⟨s, rfl⟩, h2⟩ := hq
          simp at h1 h2
          subst h1; subst h2; rfl
        · intro i
          simp only [completeInstance]
          apply Finset.card_le_one.mpr
          intro p hp q hq
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
          obtain ⟨⟨t, rfl⟩, h1⟩ := hp
          obtain ⟨⟨s, rfl⟩, h2⟩ := hq
          simp at h1 h2
          subst h1; subst h2; rfl
      have h1 := hM.2 _ hid
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)] at h1
      simp at h1
      have h2 : M.card ≤ (coveredAds M).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1)
        · intro p hp
          simp only [coveredAds, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          exact ⟨p.2, hp⟩
        · intro p hp q hq hpq
          have h3 := hM.1.2.1 p.1
          exact Finset.card_le_one.mp h3 p (by simpa using Finset.mem_coe.mp hp) q (by simp only [Finset.mem_filter]; exact ⟨Finset.mem_coe.mp hq, hpq.symm⟩)
      omega
  rw [hcov]
  simp [completeInstance]

lemma pow_le_exp_neg_one (N : ℕ) (hN : 0 < N) : (1 - 1 / (N:ℝ)) ^ N ≤ Real.exp (-1) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have h1 : 1 - 1 / (N:ℝ) ≤ Real.exp (-(1 / (N:ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (N:ℝ)))
    linarith
  have h0 : 0 ≤ 1 - 1 / (N:ℝ) := by
    have : 1 / (N:ℝ) ≤ 1 := by
      rw [div_le_one hN']; exact_mod_cast hN
    linarith
  calc (1 - 1 / (N:ℝ)) ^ N ≤ (Real.exp (-(1 / (N:ℝ)))) ^ N := pow_le_pow_left₀ h0 h1 N
    _ = Real.exp (-1) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma exp_neg_one_mul_le_pow (N : ℕ) (hN : 0 < N) :
    Real.exp (-1) * (1 - 1 / (N:ℝ)) ≤ (1 - 1 / (N:ℝ)) ^ N := by
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this; simp
  · have hN' : (2:ℝ) ≤ N := by exact_mod_cast h
    set p : ℝ := 1 - 1 / (N:ℝ) with hp
    have hp0 : 0 < p := by
      rw [hp]
      have : 1 / (N:ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have hpinv : p⁻¹ = (N:ℝ) / (N - 1) := by
      rw [hp]; field_simp
    have hlog : Real.log p⁻¹ ≤ p⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hp0)
    rw [Real.log_inv, hpinv] at hlog
    have hlog2 : ((N:ℝ) - 1) * Real.log p ≥ -1 := by
      have h1 : (N:ℝ) - 1 > 0 := by linarith
      have : -Real.log p ≤ 1 / ((N:ℝ) - 1) := by
        have e : (N:ℝ) / (N - 1) - 1 = 1 / ((N:ℝ) - 1) := by field_simp; ring
        linarith
      rw [le_div_iff₀ h1] at this
      nlinarith
    have hpow : p ^ (N - 1) = Real.exp (((N - 1 : ℕ) : ℝ) * Real.log p) := by
      rw [Real.exp_nat_mul, Real.exp_log hp0]
    have hcast : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h3 : Real.exp (-1) ≤ p ^ (N - 1) := by
      rw [hpow, hcast]; exact Real.exp_le_exp.mpr hlog2
    calc Real.exp (-1) * p ≤ p ^ (N - 1) * p := mul_le_mul_of_nonneg_right h3 hp0.le
      _ = p ^ N := by
        rw [← pow_succ]; congr 1; omega

lemma occ_le_succ {Ω : Type} [Fintype Ω] (n : ℕ) (B : Finset Ω) (x y : Fin n → Ω) (i : Fin n)
    (hi : ∀ j, j ≠ i → x j = y j) : occ n B x ≤ occ n B y + 1 := by
  unfold occ
  have hsub : B.filter (fun b => ∃ t, x t = b) ⊆ insert (x i) (B.filter (fun b => ∃ t, y t = b)) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbB, t, ht⟩ := hb
    rw [Finset.mem_insert]
    by_cases hti : t = i
    · left; rw [← ht, hti]
    · right
      rw [Finset.mem_filter]
      exact ⟨hbB, t, by rw [← hi t hti]; exact ht⟩
  calc _ ≤ (insert (x i) (B.filter (fun b => ∃ t, y t = b))).card := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _

lemma occ_diffOne {Ω : Type} [Fintype Ω] (n : ℕ) (B : Finset Ω) (x y : Fin n → Ω)
    (h : DiffOne x y) : |(occ n B x : ℝ) - occ n B y| ≤ 1 := by
  obtain ⟨i, hi⟩ := h
  have h1 := occ_le_succ n B x y i hi
  have h2 := occ_le_succ n B y x i (fun j hj => (hi j hj).symm)
  have h1' : (occ n B x : ℝ) ≤ occ n B y + 1 := by exact_mod_cast h1
  have h2' : (occ n B y : ℝ) ≤ occ n B x + 1 := by exact_mod_cast h2
  rw [abs_le]; constructor <;> linarith

lemma avg_occ {Ω : Type} [Fintype Ω] [Nonempty Ω] (n : ℕ) (B : Finset Ω) :
    avg (fun ω : Fin n → Ω => (occ n B ω : ℝ)) = B.card * (1 - (1 - 1 / (Fintype.card Ω : ℝ)) ^ n) :=
  expect_occ n B

lemma occ_concentration {Ω : Type} [Fintype Ω] (n : ℕ) (hn : 0 < n) (hcard : Fintype.card Ω = n)
    (B : Finset Ω) (ε : ℝ) (hε : 0 < ε) :
    (1 : ℝ) - 2 * Real.exp (-2 * ε^2 * n) ≤
      ((Finset.univ.filter fun ω : Fin n → Ω =>
        (B.card : ℝ) * (1 - Real.exp (-1)) - ε * (n : ℝ) ≤ (occ n B ω : ℝ) ∧
        (occ n B ω : ℝ) ≤ (B.card : ℝ) * (1 - Real.exp (-1) + 1 / (Real.exp 1 * (n : ℝ))) + ε * (n : ℝ)).card : ℝ)
        / Fintype.card (Fin n → Ω) := by
  haveI : Nonempty Ω := by rw [← Fintype.card_pos_iff, hcard]; exact hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : (0 : ℝ) < Fintype.card (Fin n → Ω) := by exact_mod_cast Fintype.card_pos
  set f : (Fin n → Ω) → ℝ := fun ω => (occ n B ω : ℝ) with hf
  have hfd : ∀ x y, DiffOne x y → |f x - f y| ≤ 1 := fun x y h => occ_diffOne n B x y h
  have hs : 0 ≤ ε * (n:ℝ) := by positivity
  have hU := mcd_tail n hn f hfd (ε * n) hs
  have hL := mcd_tail_lower n hn f hfd (ε * n) hs
  have hexp : Real.exp (-2 * (ε * n)^2 / n) = Real.exp (-2 * ε^2 * n) := by
    congr 1; field_simp
  rw [hexp] at hU hL
  have hmu : avg f = B.card * (1 - (1 - 1 / (n : ℝ)) ^ n) := by
    rw [hf, avg_occ, hcard]
  set U := Finset.univ.filter fun x => ε * n ≤ f x - avg f with hUdef
  set L := Finset.univ.filter fun x => f x - avg f ≤ -(ε * n) with hLdef
  set G := Finset.univ.filter fun ω : Fin n → Ω =>
        (B.card : ℝ) * (1 - Real.exp (-1)) - ε * (n : ℝ) ≤ (occ n B ω : ℝ) ∧
        (occ n B ω : ℝ) ≤ (B.card : ℝ) * (1 - Real.exp (-1) + 1 / (Real.exp 1 * (n : ℝ))) + ε * (n : ℝ) with hG
  have hsub : (Finset.univ : Finset (Fin n → Ω)) ⊆ G ∪ (U ∪ L) := by
    intro x _
    by_cases h1 : ε * n ≤ f x - avg f
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (by rw [hUdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h1⟩))
    by_cases h2 : f x - avg f ≤ -(ε * n)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (by rw [hLdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h2⟩))
    apply Finset.mem_union_left
    rw [hG, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hpe := pow_le_exp_neg_one n hn
      have hB : (0:ℝ) ≤ B.card := Nat.cast_nonneg _
      have : (B.card : ℝ) * (1 - Real.exp (-1)) ≤ avg f := by
        rw [hmu]; nlinarith
      push_neg at h2
      show _ ≤ f x
      linarith
    · have hpe := exp_neg_one_mul_le_pow n hn
      have hB : (0:ℝ) ≤ B.card := Nat.cast_nonneg _
      have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
      have : avg f ≤ (B.card : ℝ) * (1 - Real.exp (-1) + 1 / (Real.exp 1 * (n : ℝ))) := by
        rw [hmu]
        have : 1 / (Real.exp 1 * (n : ℝ)) = Real.exp (-1) * (1 / n) := by
          rw [Real.exp_neg]; field_simp
        rw [this]
        nlinarith
      push_neg at h1
      show f x ≤ _
      linarith
  have hcardle : (Fintype.card (Fin n → Ω) : ℝ) ≤ G.card + U.card + L.card := by
    have h1 : (Finset.univ : Finset (Fin n → Ω)).card ≤ (G ∪ (U ∪ L)).card := Finset.card_le_card hsub
    have h2 : (G ∪ (U ∪ L)).card ≤ G.card + (U ∪ L).card := Finset.card_union_le _ _
    have h3 : (U ∪ L).card ≤ U.card + L.card := Finset.card_union_le _ _
    have : Fintype.card (Fin n → Ω) ≤ G.card + U.card + L.card := by
      rw [Finset.card_univ] at h1; omega
    exact_mod_cast this
  have hU' : (U.card : ℝ) ≤ Real.exp (-2 * ε^2 * n) * Fintype.card (Fin n → Ω) := by
    rwa [div_le_iff₀ hC] at hU
  have hL' : (L.card : ℝ) ≤ Real.exp (-2 * ε^2 * n) * Fintype.card (Fin n → Ω) := by
    rwa [div_le_iff₀ hC] at hL
  rw [le_div_iff₀ hC]
  nlinarith

theorem fact_1_core (n : ℕ) (hn : 0 < n) (B : Finset (Fin n))
    (ε : ℝ) (hε : 0 < ε) :
    uniformProbability (fun ω : Fin n → Fin n =>
      (B.card : ℝ) * (1 - Real.exp (-1)) - ε * (n : ℝ) ≤
        (occupiedIn n B ω : ℝ) ∧
      (occupiedIn n B ω : ℝ) ≤
        (B.card : ℝ) *
          (1 - Real.exp (-1) + 1 / (Real.exp 1 * (n : ℝ))) + ε * (n : ℝ)) ≥
      1 - 2 * Real.exp (-(ε ^ 2) * (n : ℝ) / 2) := by
  have h := occ_concentration n hn (by simp) B ε hε
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : Real.exp (-2 * ε^2 * n) ≤ Real.exp (-(ε ^ 2) * (n : ℝ) / 2) := by
    apply Real.exp_le_exp.mpr
    have : 0 < ε^2 * n := by positivity
    nlinarith
  unfold uniformProbability
  have e : occupiedIn n B = occ n B := by
    funext ω; unfold occupiedIn occ; congr
  simp only [e]
  linarith

lemma two_exp_le (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : ⌈1 / ε^2⌉₊ ≤ n) :
    2 * Real.exp (-2 * ε^2 * n) ≤ Real.exp (-(ε^2) * n) := by
  have h1 : 1 / ε^2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hε2 : 0 < ε^2 := by positivity
  have h2 : 1 ≤ ε^2 * n := by
    rw [div_le_iff₀ hε2] at h1; linarith
  have h3 : (2:ℝ) ≤ Real.exp (ε^2 * n) := by
    have := Real.add_one_le_exp (ε^2 * n); linarith
  have h4 : Real.exp (-2 * ε^2 * n) = Real.exp (-(ε^2) * n) * Real.exp (-(ε^2 * n)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h5 : Real.exp (-(ε^2 * n)) * Real.exp (ε^2 * n) = 1 := by
    rw [← Real.exp_add]; simp
  have h6 : 2 * Real.exp (-(ε^2 * n)) ≤ 1 := by
    have := Real.exp_pos (-(ε^2 * n))
    nlinarith
  rw [h4]
  have := Real.exp_pos (-(ε^2) * n)
  nlinarith

theorem bounding_alg_core :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option A) (hlabel : IsLabelling inst M label),
        runProbability inst (fun ω =>
          (1 - Real.exp (-1)) * (coveredAds M).card - ε * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ)) := by
  intro ε hε
  refine ⟨ε^2, by positivity, ⌈1 / ε^2⌉₊, ?_⟩
  intro A I _ _ inst hn M hM label hlabel
  have hocc := occ_concentration inst.n inst.n_pos (card_copy inst) (labB inst label) ε hε
  have hcl := labB_card inst M label hlabel
  have hC : (0 : ℝ) < Fintype.card (Fin inst.n → inst.Copy) := by
    have : 0 < Fintype.card (Fin inst.n → inst.Copy) := by
      rw [Fintype.card_fun, Fintype.card_fin, card_copy]; exact pow_pos inst.n_pos _
    exact_mod_cast this
  have h2 := two_exp_le ε hε inst.n hn
  unfold runProbability uniformProbability
  set G := Finset.univ.filter fun ω : Fin inst.n → inst.Copy =>
        ((labB inst label).card : ℝ) * (1 - Real.exp (-1)) - ε * (inst.n : ℝ) ≤ (occ inst.n (labB inst label) ω : ℝ) ∧
        (occ inst.n (labB inst label) ω : ℝ) ≤ ((labB inst label).card : ℝ) * (1 - Real.exp (-1) + 1 / (Real.exp 1 * (inst.n : ℝ))) + ε * (inst.n : ℝ) with hG
  have hsub : G ⊆ Finset.univ.filter fun ω : Fin inst.n → inst.Copy =>
          (1 - Real.exp (-1)) * (coveredAds M).card - ε * (inst.n : ℝ) ≤ (algorithm inst label ω : ℝ) := by
    intro ω hω
    rw [hG, Finset.mem_filter] at hω
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [algorithm_eq_occ inst label hlabel.2 ω, ← hcl]
    have := hω.2.1
    linarith
  have hle := Finset.card_le_card hsub
  have hle' := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hle) hC.le
  linarith


noncomputable def degA (N : Finset (A × I)) (a : A) : ℕ := (N.filter fun p => p.1 = a).card
noncomputable def degT (N : Finset (A × I)) (i : I) : ℕ := (N.filter fun p => p.2 = i).card

lemma isBM_iff (inst : Instance A I) (N : Finset (A × I)) :
    IsBMatching inst N ↔ (N ⊆ inst.E ∧ (∀ a, degA N a ≤ 1) ∧ ∀ i, degT N i ≤ inst.e i) := by
  unfold IsBMatching degA degT
  constructor <;> intro h <;> convert h

lemma degA_insert (N : Finset (A × I)) (x : A × I) (hx : x ∉ N) (a : A) :
    degA (insert x N) a = degA N a + if x.1 = a then 1 else 0 := by
  unfold degA
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hx])]
  · simp

lemma degT_insert (N : Finset (A × I)) (x : A × I) (hx : x ∉ N) (i : I) :
    degT (insert x N) i = degT N i + if x.2 = i then 1 else 0 := by
  unfold degT
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hx])]
  · simp

lemma degA_erase (N : Finset (A × I)) (x : A × I) (hx : x ∈ N) (a : A) :
    degA (N.erase x) a + (if x.1 = a then 1 else 0) = degA N a := by
  unfold degA
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (by simp [hx, h])]
    have : 0 < (N.filter fun p => p.1 = a).card := Finset.card_pos.mpr ⟨x, by simp [hx, h]⟩
    omega
  · simp [Finset.erase_eq_of_notMem (by simp [h] : x ∉ N.filter fun p => p.1 = a)]

lemma degT_erase (N : Finset (A × I)) (x : A × I) (hx : x ∈ N) (i : I) :
    degT (N.erase x) i + (if x.2 = i then 1 else 0) = degT N i := by
  unfold degT
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (by simp [hx, h])]
    have : 0 < (N.filter fun p => p.2 = i).card := Finset.card_pos.mpr ⟨x, by simp [hx, h]⟩
    omega
  · simp [Finset.erase_eq_of_notMem (by simp [h] : x ∉ N.filter fun p => p.2 = i)]

def Dset (inst : Instance A I) (M : Finset (A × I)) : ℕ → Set (Option (A ⊕ I))
  | 0 => {none}
  | k+1 => Dset inst M k ∪ {y | ∃ x ∈ Dset inst M k, ResidualStep inst M x y}

lemma Dset_mono (inst : Instance A I) (M : Finset (A × I)) {k l : ℕ} (h : k ≤ l) :
    Dset inst M k ⊆ Dset inst M l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Set.subset_union_left

lemma reach_Dset (inst : Instance A I) (M : Finset (A × I)) (y : Option (A ⊕ I))
    (h : Relation.ReflTransGen (ResidualStep inst M) none y) : ∃ k, y ∈ Dset inst M k := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hr ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k+1, Or.inr ⟨_, hk, hr⟩⟩

def Good (inst : Instance A I) (M N : Finset (A × I)) : Prop :=
  N ⊆ inst.E ∧ (∀ a, degA N a ≤ 1) ∧ (∀ i, degT N i = degT M i) ∧ N.card = M.card

def Cond (inst : Instance A I) (M : Finset (A × I)) : Option (A ⊕ I) → Finset (A × I) → Prop
  | none, N => Good inst M N
  | some (.inl a), N => Good inst M N ∧ degA N a = 0
  | some (.inr t), N => N ⊆ inst.E ∧ (∀ a, degA N a ≤ 1) ∧ (∀ i, i ≠ t → degT N i = degT M i) ∧
      degT N t = degT M t + 1 ∧ N.card = M.card + 1

lemma main_inv (inst : Instance A I) (M : Finset (A × I)) (hM : IsBMatching inst M) (k : ℕ) :
    ∀ x ∈ Dset inst M k, ∃ N : Finset (A × I), Cond inst M x N ∧
      ∀ b : A, some (Sum.inl b) ∉ Dset inst M k →
        N.filter (fun p => p.1 = b) = M.filter (fun p => p.1 = b) := by
  obtain ⟨hME, hMA, hMT⟩ := (isBM_iff inst M).mp hM
  induction k with
  | zero =>
    intro x hx
    have : x = none := hx
    subst this
    refine ⟨M, ⟨hME, hMA, fun i => rfl, rfl⟩, fun b _ => rfl⟩
  | succ k ih =>
    intro x hx
    rcases hx with hx | ⟨y, hy, hR⟩
    · obtain ⟨N, hN, ht⟩ := ih x hx
      exact ⟨N, hN, fun b hb => ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))⟩
    · by_cases hxk : x ∈ Dset inst M k
      · obtain ⟨N, hN, ht⟩ := ih x hxk
        exact ⟨N, hN, fun b hb => ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))⟩
      obtain ⟨N, hN, ht⟩ := ih y hy
      rcases y with _ | (a | t) <;> rcases x with _ | (a' | t') <;> simp only [ResidualStep] at hR
      · -- none -> inl a'
        refine ⟨N, ⟨hN, ?_⟩, fun b hb => ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))⟩
        have h1 := ht a' hxk
        have : degA N a' = degA M a' := by unfold degA; rw [h1]
        rw [this]
        unfold degA; exact hR
      · -- inl a -> inr t'
        obtain ⟨hEa, hnM⟩ := hR
        obtain ⟨hN1, hN2⟩ := hN
        obtain ⟨hNE, hNA, hNT, hNc⟩ := hN1
        have hnot : (a, t') ∉ N := by
          intro hmem
          have : 0 < degA N a := Finset.card_pos.mpr ⟨(a, t'), by simp [hmem]⟩
          omega
        refine ⟨insert (a, t') N, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · exact Finset.insert_subset hEa hNE
        · intro b
          rw [degA_insert N _ hnot]
          by_cases hab : a = b
          · subst hab; simp [hN2]
          · simp [hab]; exact hNA b
        · intro i hi
          rw [degT_insert N _ hnot]
          have : ¬ (t' = i) := fun h => hi h.symm
          simp [this, hNT i]
        · rw [degT_insert N _ hnot]; simp [hNT t']
        · rw [Finset.card_insert_of_notMem hnot, hNc]
        · intro b hb
          have hba : b ≠ a := fun h => hb (Dset_mono inst M (Nat.le_succ k) (h ▸ hy))
          rw [Finset.filter_insert]
          simp only [hba.symm, if_false]
          exact ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))
      · -- inr t -> inl a'
        obtain ⟨hNE, hNA, hNT, hNt, hNc⟩ := hN
        have hmemM : (a', t) ∈ M := hR
        have h1 := ht a' hxk
        have hmemN : (a', t) ∈ N := by
          have : (a', t) ∈ M.filter (fun p => p.1 = a') := by simp [hmemM]
          rw [← h1] at this
          exact (Finset.mem_filter.mp this).1
        have hdA : degA N a' = degA M a' := by unfold degA; rw [h1]
        refine ⟨N.erase (a', t), ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · exact (Finset.erase_subset _ _).trans hNE
        · intro b
          have := degA_erase N (a', t) hmemN b
          have := hNA b
          omega
        · intro i
          have := degT_erase N (a', t) hmemN i
          by_cases hi : t = i
          · subst hi; simp at this; omega
          · simp [hi] at this
            have hi' : i ≠ t := fun h => hi h.symm
            rw [this]; exact hNT i hi'
        · rw [Finset.card_erase_of_mem hmemN]; omega
        · have := degA_erase N (a', t) hmemN a'
          simp at this
          have h2 := hMA a'
          have h3 : 0 < degA M a' := Finset.card_pos.mpr ⟨(a', t), by simp [hmemM]⟩
          omega
        · intro b hb
          have hba : b ≠ a' := fun h => hb (Or.inr ⟨_, hy, by rw [h]; exact hR⟩)
          rw [Finset.filter_erase]
          have h2 := ht b (fun h => hb (Dset_mono inst M (Nat.le_succ k) h))
          rw [h2]
          have : (a', t) ∉ M.filter (fun p => p.1 = b) := by simp [hba.symm]
          exact Finset.erase_eq_of_notMem this

lemma sat_type (inst : Instance A I) (M : Finset (A × I)) (hM : IsMaxBMatching inst M) (t : I)
    (h : typeInSourceSide inst M t) : degT M t = inst.e t := by
  obtain ⟨k, hk⟩ := reach_Dset inst M _ h
  obtain ⟨N, hN, _⟩ := main_inv inst M hM.1 k _ hk
  obtain ⟨hNE, hNA, hNT, hNt, hNc⟩ := hN
  obtain ⟨hME, hMA, hMT⟩ := (isBM_iff inst M).mp hM.1
  by_contra hne
  have hlt : degT M t < inst.e t := lt_of_le_of_ne (hMT t) hne
  have hNB : IsBMatching inst N := by
    rw [isBM_iff]
    refine ⟨hNE, hNA, fun i => ?_⟩
    by_cases hi : i = t
    · subst hi; omega
    · rw [hNT i hi]; exact hMT i
  have := hM.2 N hNB
  omega

lemma ad_fact1 (inst : Instance A I) (M : Finset (A × I)) (a : A) (h : degA M a = 0) :
    adInSourceSide inst M a := by
  apply Relation.ReflTransGen.single
  show (M.filter fun (p : A × I) => p.1 = a).card = 0
  exact h

lemma ad_fact2 (inst : Instance A I) (M : Finset (A × I)) (a : A) (i : I) (h : (a, i) ∈ M)
    (hi : typeInSourceSide inst M i) : adInSourceSide inst M a :=
  Relation.ReflTransGen.tail hi (show (a, i) ∈ M from h)

lemma ad_fact3 (inst : Instance A I) (M : Finset (A × I)) (hM : IsBMatching inst M)
    (a : A) (i : I) (h : (a, i) ∈ M) (ha : adInSourceSide inst M a) :
    typeInSourceSide inst M i := by
  obtain ⟨hME, hMA, hMT⟩ := (isBM_iff inst M).mp hM
  rcases Relation.ReflTransGen.cases_tail ha with h0 | ⟨c, hc, hr⟩
  · exact absurd h0 (by simp)
  · rcases c with _ | (a1 | i1)
    · exfalso
      have h1 : (M.filter fun (p : A × I) => p.1 = a).card = 0 := hr
      have : 0 < degA M a := Finset.card_pos.mpr ⟨(a, i), by simp [h]⟩
      unfold degA at this
      omega
    · exact absurd hr (by simp [ResidualStep])
    · have h1 : (a, i1) ∈ M := hr
      have : (a, i) = (a, i1) := by
        have := Finset.card_le_one.mp (hMA a) (a, i) (by simp [h]) (a, i1) (by simp [h1])
        exact this
      have e : i = i1 := (Prod.mk.inj this).2
      subst e
      exact hc

lemma ad_to_type (inst : Instance A I) (M : Finset (A × I)) (hM : IsBMatching inst M)
    (a : A) (i : I) (hE : (a, i) ∈ inst.E) (ha : adInSourceSide inst M a) :
    typeInSourceSide inst M i := by
  by_cases hmem : (a, i) ∈ M
  · exact ad_fact3 inst M hM a i hmem ha
  · exact Relation.ReflTransGen.tail ha (show (a, i) ∈ inst.E ∧ (a, i) ∉ M from ⟨hE, hmem⟩)

lemma coveredAds_eq_image (M : Finset (A × I)) : coveredAds M = M.image Prod.fst := by
  ext a
  simp [coveredAds]

theorem cut_identity_core (A I : Type) [Fintype A] [Fintype I]
    (inst : Instance A I) (M : Finset (A × I)) (hM : IsMaxBMatching inst M) :
    (∀ a i, (a, i) ∈ inst.E → adInSourceSide inst M a → typeInSourceSide inst M i) ∧
      (coveredAds M).card =
        (adsInSinkSide inst M).card +
          ∑ i ∈ typesInSourceSide inst M, inst.e i := by
  refine ⟨fun a i hE ha => ad_to_type inst M hM.1 a i hE ha, ?_⟩
  obtain ⟨hME, hMA, hMT⟩ := (isBM_iff inst M).mp hM.1
  have hinj : Set.InjOn Prod.fst (M : Set (A × I)) := by
    intro p hp q hq hpq
    exact Finset.card_le_one.mp (hMA p.1) p (by simp [Finset.mem_coe.mp hp])
      q (by simp [Finset.mem_coe.mp hq]; exact hpq.symm)
  have h1 : (coveredAds M).card = M.card := by
    rw [coveredAds_eq_image, Finset.card_image_of_injOn hinj]
  have h2 := Finset.card_filter_add_card_filter_not (s := M) (fun p : A × I => typeInSourceSide inst M p.2)
  -- reachable-type edges
  have h3 : (M.filter fun p : A × I => typeInSourceSide inst M p.2).card =
      ∑ i ∈ typesInSourceSide inst M, inst.e i := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := typesInSourceSide inst M)]
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : typeInSourceSide inst M i := by simpa [typesInSourceSide] using hi
      rw [← sat_type inst M hM i hi']
      unfold degT
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨h, by rw [h']; exact hi'⟩, h'⟩
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      simp [typesInSourceSide, hp.2]
  have h4 : (M.filter fun p : A × I => ¬ typeInSourceSide inst M p.2).card =
      (adsInSinkSide inst M).card := by
    have himg : (M.filter fun p : A × I => ¬ typeInSourceSide inst M p.2).image Prod.fst
        = adsInSinkSide inst M := by
      ext a
      simp only [Finset.mem_image, Finset.mem_filter, adsInSinkSide, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨p, ⟨hp, hpt⟩, rfl⟩ hra
        exact hpt (ad_fact3 inst M hM.1 p.1 p.2 hp hra)
      · intro hra
        have hdeg : degA M a ≠ 0 := fun h => hra (ad_fact1 inst M a h)
        obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hdeg)
        rw [Finset.mem_filter] at hp
        refine ⟨p, ⟨hp.1, fun hpt => hra ?_⟩, hp.2⟩
        rw [← hp.2]
        exact ad_fact2 inst M p.1 p.2 hp.1 hpt
    rw [← himg, Finset.card_image_of_injOn]
    intro p hp q hq hpq
    exact hinj (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).1) hpq
  omega


noncomputable def cnt {Ω : Type} [Fintype Ω] (n : ℕ) (P : Ω → Prop) (ω : Fin n → Ω) : ℕ :=
  (Finset.univ.filter fun t : Fin n => P (ω t)).card

lemma cnt_le_succ {Ω : Type} [Fintype Ω] (n : ℕ) (P : Ω → Prop) (x y : Fin n → Ω) (i : Fin n)
    (hi : ∀ j, j ≠ i → x j = y j) : cnt n P x ≤ cnt n P y + 1 := by
  unfold cnt
  have hsub : (Finset.univ.filter fun t : Fin n => P (x t)) ⊆
      insert i (Finset.univ.filter fun t : Fin n => P (y t)) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_insert, Finset.mem_filter]
    by_cases h : t = i
    · left; exact h
    · right; exact ⟨Finset.mem_univ _, by rw [← hi t h]; exact ht.2⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _

lemma card_slice {Ω : Type} [Fintype Ω] (n : ℕ) (P : Ω → Prop) (t : Fin n) :
    (Finset.univ.filter fun ω : Fin n → Ω => P (ω t)).card
      = (Finset.univ.filter P).card * Fintype.card Ω ^ (n - 1) := by
  have h : (Finset.univ.filter fun ω : Fin n → Ω => P (ω t))
      = Fintype.piFinset (fun s => if s = t then Finset.univ.filter P else Finset.univ) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h s
      by_cases hs : s = t
      · subst hs; simpa using h
      · simp [hs]
    · intro h
      have := h t
      simpa using this
  rw [h, Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t)]
  simp only [if_true]
  rw [Finset.prod_congr rfl (g := fun _ => Fintype.card Ω)]
  · simp
  · intro s hs
    have : s ≠ t := Finset.ne_of_mem_erase hs
    simp [this]

lemma avg_cnt {Ω : Type} [Fintype Ω] (n : ℕ) (hn : 0 < n) (hcard : Fintype.card Ω = n)
    (P : Ω → Prop) :
    (∑ ω : Fin n → Ω, (cnt n P ω : ℝ)) / (Fintype.card (Fin n → Ω) : ℝ)
      = (Finset.univ.filter P).card := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : ∑ ω : Fin n → Ω, (cnt n P ω : ℝ) = ∑ t : Fin n, ((Finset.univ.filter fun ω : Fin n → Ω => P (ω t)).card : ℝ) := by
    unfold cnt
    simp only [Finset.card_filter]
    push_cast
    rw [Finset.sum_comm]
  simp only [card_slice] at h1
  rw [h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.card_fun, Fintype.card_fin, hcard]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  push_cast
  rw [pow_succ]
  field_simp


lemma card_Bc (inst : Instance A I) (M : Finset (A × I)) :
    (Finset.univ.filter fun c : inst.Copy => typeInSourceSide inst M c.1).card
      = ∑ i ∈ typesInSourceSide inst M, inst.e i := by
  have : (Finset.univ.filter fun c : inst.Copy => typeInSourceSide inst M c.1)
      = (typesInSourceSide inst M).sigma (fun i => (Finset.univ : Finset (Fin (inst.e i)))) := by
    ext ⟨i, j⟩
    simp [typesInSourceSide]
  rw [this, Finset.card_sigma]
  simp

lemma optimum_le (inst : Instance A I) (M : Finset (A × I)) (hM : IsBMatching inst M)
    (ω : Fin inst.n → inst.Copy) :
    optimum inst ω ≤ (adsInSinkSide inst M).card +
      cnt inst.n (fun c : inst.Copy => typeInSourceSide inst M c.1) ω := by
  unfold optimum
  apply Finset.sup_le
  intro R _
  split_ifs with h
  · obtain ⟨hE, hA, hT⟩ := h
    have hsplit := Finset.card_filter_add_card_filter_not (s := R)
      (fun p : A × Fin inst.n => adInSourceSide inst M p.1)
    have h1 : (R.filter fun p : A × Fin inst.n => ¬ adInSourceSide inst M p.1).card
        ≤ (adsInSinkSide inst M).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
        simp [adsInSinkSide, hp'.2]
      · intro p hp q hq hpq
        have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
        have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
        exact Finset.card_le_one.mp (hA p.1) p (by simp [hp'.1])
          q (by simp [hq'.1]; exact hpq.symm)
    have h2 : (R.filter fun p : A × Fin inst.n => adInSourceSide inst M p.1).card
        ≤ cnt inst.n (fun c : inst.Copy => typeInSourceSide inst M c.1) ω := by
      unfold cnt
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro p hp
        have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        exact ad_to_type inst M hM p.1 (ω p.2).1 (hE p hp'.1) hp'.2
      · intro p hp q hq hpq
        have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
        have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
        exact Finset.card_le_one.mp (hT p.2) p (by simp [hp'.1])
          q (by simp [hq'.1]; exact hpq.symm)
    omega
  · exact Nat.zero_le _

theorem opt_bound_core :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M),
        runProbability inst (fun ω =>
          (optimum inst ω : ℝ) ≤ (coveredAds M).card + ε * (inst.n : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ)) := by
  intro ε hε
  refine ⟨ε^2, by positivity, 0, ?_⟩
  intro A I _ _ inst _ M hM
  have hnpos := inst.n_pos
  have hnR : (0:ℝ) < inst.n := by exact_mod_cast hnpos
  have hC : (0 : ℝ) < Fintype.card (Fin inst.n → inst.Copy) := by
    have : 0 < Fintype.card (Fin inst.n → inst.Copy) := by
      rw [Fintype.card_fun, Fintype.card_fin, card_copy]; exact pow_pos inst.n_pos _
    exact_mod_cast this
  haveI : Nonempty inst.Copy := by
    rw [← Fintype.card_pos_iff, card_copy]; exact inst.n_pos
  set P : inst.Copy → Prop := fun c => typeInSourceSide inst M c.1 with hP
  set f : (Fin inst.n → inst.Copy) → ℝ := fun ω => (cnt inst.n P ω : ℝ) with hf
  have hfd : ∀ x y, DiffOne x y → |f x - f y| ≤ 1 := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hxy
    have h1 := cnt_le_succ inst.n P x y i hi
    have h2 := cnt_le_succ inst.n P y x i (fun j hj => (hi j hj).symm)
    have h1' : (cnt inst.n P x : ℝ) ≤ cnt inst.n P y + 1 := by exact_mod_cast h1
    have h2' : (cnt inst.n P y : ℝ) ≤ cnt inst.n P x + 1 := by exact_mod_cast h2
    simp only [hf]
    rw [abs_le]; constructor <;> linarith
  have havg : avg f = (Finset.univ.filter P).card := avg_cnt inst.n hnpos (card_copy inst) P
  have hs : 0 ≤ ε * (inst.n:ℝ) := by positivity
  have hU := mcd_tail inst.n hnpos f hfd (ε * inst.n) hs
  have hexp : Real.exp (-2 * (ε * inst.n)^2 / inst.n) = Real.exp (-2 * ε^2 * inst.n) := by
    congr 1; field_simp
  rw [hexp] at hU
  have hcut := (cut_identity_core A I inst M hM).2
  have hBc := card_Bc inst M
  set U := Finset.univ.filter fun x => ε * inst.n ≤ f x - avg f with hUdef
  set E := Finset.univ.filter fun ω : Fin inst.n → inst.Copy =>
    (optimum inst ω : ℝ) ≤ (coveredAds M).card + ε * (inst.n : ℝ) with hE
  have hsub : (Finset.univ : Finset (Fin inst.n → inst.Copy)) ⊆ E ∪ U := by
    intro ω _
    by_cases h1 : ε * inst.n ≤ f ω - avg f
    · exact Finset.mem_union_right _ (by rw [hUdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h1⟩)
    · apply Finset.mem_union_left
      rw [hE, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hle := optimum_le inst M hM.1 ω
      have hle' : (optimum inst ω : ℝ) ≤ (adsInSinkSide inst M).card + (cnt inst.n P ω : ℝ) := by
        exact_mod_cast hle
      push_neg at h1
      have hcut' : ((coveredAds M).card : ℝ) = (adsInSinkSide inst M).card +
          ((Finset.univ.filter P).card : ℝ) := by
        rw [hcut, ← hBc]; push_cast; rfl
      have : f ω < (Finset.univ.filter P).card + ε * inst.n := by
        rw [← havg]; linarith
      simp only [hf] at this
      linarith
  have hcard : (Fintype.card (Fin inst.n → inst.Copy) : ℝ) ≤ E.card + U.card := by
    have h1 : (Finset.univ : Finset (Fin inst.n → inst.Copy)).card ≤ (E ∪ U).card := Finset.card_le_card hsub
    have h2 : (E ∪ U).card ≤ E.card + U.card := Finset.card_union_le _ _
    have : Fintype.card (Fin inst.n → inst.Copy) ≤ E.card + U.card := by
      rw [Finset.card_univ] at h1; omega
    exact_mod_cast this
  have hU' : (U.card : ℝ) ≤ Real.exp (-2 * ε^2 * inst.n) * Fintype.card (Fin inst.n → inst.Copy) := by
    rwa [div_le_iff₀ hC] at hU
  have hexp2 : Real.exp (-2 * ε^2 * inst.n) ≤ Real.exp (-(ε^2) * inst.n) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ ε^2 * inst.n := by positivity
    nlinarith
  unfold runProbability uniformProbability
  have hfin : (1 : ℝ) - Real.exp (-(ε^2) * inst.n) ≤ (E.card : ℝ) / Fintype.card (Fin inst.n → inst.Copy) := by
    rw [le_div_iff₀ hC]
    nlinarith [Real.exp_pos (-(ε^2) * inst.n)]
  exact hfin

end OnlineStochMatching.SuggestedMatching

open OnlineStochMatching.SuggestedMatching


theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M),
        runProbability inst (fun ω =>
          (optimum inst ω : ℝ) ≤ (coveredAds M).card + ε * (inst.n : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ)) := by
  exact opt_bound_core
