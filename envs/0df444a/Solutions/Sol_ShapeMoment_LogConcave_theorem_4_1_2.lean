-- Prove2me | solution 2 for ShapeMoment.LogConcave.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:23.58161+00:00
-- url     : https://prove2.me/submissions/2349e610-9f34-4729-b1c3-3377199c9555

import Mathlib
import Definitions.Def_ShapeMoment_LogConcave_Model
import Theorems.Thm_ShapeMoment_LogConcave_geometric_of_tight
import Theorems.Thm_ShapeMoment_LogConcave_proposition_2_4

-- carved verbatim out of submission 7214b137-5830-4930-be73-4639e74973cf, lines 639-680

section
set_option autoImplicit false
open ShapeMoment.LogConcave

lemma sm_ext_out {n : ℕ} (x : Fin n → ℝ) (i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ n)) : ext x i = 0 := by
  unfold ext
  rw [dif_neg h]

lemma sm_ext_zero_of_out {n : ℕ} (x : Fin n → ℝ) (k ℓ : ℕ) (hk : 1 ≤ k) (hle : ℓ ≤ n)
    (hzero : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0) (i : ℕ)
    (hi : ¬ (k ≤ i ∧ i ≤ ℓ)) : ext x i = 0 := by
  by_cases h : 1 ≤ i ∧ i ≤ n
  · have := hzero ⟨i - 1, by omega⟩ (by simp only; omega)
    unfold ext
    rw [dif_pos h]; exact this
  · exact sm_ext_out x i h

lemma sm_ext_add {n : ℕ} (x y : Fin n → ℝ) (i : ℕ) : ext (x + y) i = ext x i + ext y i := by
  unfold ext
  split_ifs <;> simp

lemma sm_ext_smul {n : ℕ} (s : ℝ) (x : Fin n → ℝ) (i : ℕ) : ext (s • x) i = s * ext x i := by
  unfold ext
  split_ifs <;> simp

lemma sm_moment_add {n : ℕ} (x y : Fin n → ℝ) (i : ℕ) :
    moment (x + y) i = moment x i + moment y i := by
  simp [moment, mul_add, Finset.sum_add_distrib]

lemma sm_moment_smul {n : ℕ} (s : ℝ) (x : Fin n → ℝ) (i : ℕ) :
    moment (s • x) i = s * moment x i := by
  simp [moment, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma sm_Q_le (a b c p q r : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hac : a * c = b ^ 2)
    (hlin : c * p + a * r = 2 * b * q) : p * r ≤ q ^ 2 := by
  have h1 : (c * p) * (a * r) ≤ ((c * p + a * r) / 2) ^ 2 := by
    nlinarith [sq_nonneg (c * p - a * r)]
  have h2 : (c * p + a * r) / 2 = b * q := by linarith
  rw [h2] at h1
  have h3 : b ^ 2 * (p * r) ≤ b ^ 2 * q ^ 2 := by
    calc b ^ 2 * (p * r) = (c * p) * (a * r) := by rw [← hac]; ring
      _ ≤ (b * q) ^ 2 := h1
      _ = b ^ 2 * q ^ 2 := by ring
  exact le_of_mul_le_mul_left h3 (by positivity)

lemma sm_ev_pos (A B : ℝ) (hA : 0 < A) : ∀ᶠ s in nhds (0 : ℝ), 0 < A + s * B := by
  have hc : ContinuousAt (fun s : ℝ => A + s * B) 0 := by fun_prop
  have := ContinuousAt.eventually_lt (continuousAt_const (y := (0:ℝ)) (x := (0:ℝ))) hc (by simpa using hA)
  exact this

lemma sm_ev_lt (a b c p q r : ℝ) (h : a * c < b ^ 2) :
    ∀ᶠ s in nhds (0 : ℝ), (a + s * p) * (c + s * r) ≤ (b + s * q) ^ 2 := by
  have hf : ContinuousAt (fun s : ℝ => (a + s * p) * (c + s * r)) 0 := by fun_prop
  have hg : ContinuousAt (fun s : ℝ => (b + s * q) ^ 2) 0 := by fun_prop
  have := ContinuousAt.eventually_lt hf hg (by simpa using h)
  exact this.mono (fun s hs => hs.le)

lemma sm_perturb (n m : ℕ) (q : ℕ → ℝ) (x d : Fin n → ℝ) (k ℓ : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ)
    (hle : ℓ ≤ n) (hmom : ∀ i ≤ m, moment x i = q i)
    (hlc : ∀ j, k < j → j < ℓ → ext x (j - 1) * ext x (j + 1) ≤ ext x j ^ 2)
    (hpos : ∀ j, k ≤ j → j ≤ ℓ → 0 < ext x j)
    (hzero : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0)
    (hdmom : ∀ i ≤ m, moment d i = 0)
    (hdz : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → d j = 0)
    (hdt : ∀ j, k < j → j < ℓ → ext x (j - 1) * ext x (j + 1) = ext x j ^ 2 →
      ext x (j + 1) * ext d (j - 1) + ext x (j - 1) * ext d (j + 1) = 2 * ext x j * ext d j) :
    ∀ᶠ s in nhds (0 : ℝ), x + s • d ∈ feasLC n m q := by
  have h1 : ∀ᶠ s in nhds (0 : ℝ), ∀ j ∈ Finset.Icc k ℓ, 0 < ext x j + s * ext d j := by
    rw [Filter.eventually_all_finset]
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact sm_ev_pos _ _ (hpos j hj.1 hj.2)
  have h2 : ∀ᶠ s in nhds (0 : ℝ), ∀ j ∈ Finset.Ioo k ℓ,
      (ext x (j - 1) + s * ext d (j - 1)) * (ext x (j + 1) + s * ext d (j + 1)) ≤
        (ext x j + s * ext d j) ^ 2 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    rw [Finset.mem_Ioo] at hj
    rcases (hlc j hj.1 hj.2).lt_or_eq with hlt | heq
    · exact sm_ev_lt _ _ _ _ _ _ hlt
    · refine Filter.Eventually.of_forall (fun s => ?_)
      have hlin := hdt j hj.1 hj.2 heq
      have hQ := sm_Q_le (ext x (j - 1)) (ext x j) (ext x (j + 1)) (ext d (j - 1)) (ext d j)
        (ext d (j + 1)) (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))
        (hpos _ (by omega) (by omega)) heq (by linarith)
      have e : s * (ext x (j + 1) * ext d (j - 1) + ext x (j - 1) * ext d (j + 1)) =
          s * (2 * ext x j * ext d j) := by rw [hlin]
      nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.2 hQ), e, heq]
  filter_upwards [h1, h2] with s hs1 hs2
  refine ⟨k, ℓ, hk, hkl, hle, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [sm_moment_add, sm_moment_smul, hdmom i hi, hmom i hi]; ring
  · intro j hj1 hj2
    have := hs2 j (Finset.mem_Ioo.2 ⟨hj1, hj2⟩)
    simpa only [sm_ext_add, sm_ext_smul] using this
  · intro j hj1 hj2
    have := hs1 j (Finset.mem_Icc.2 ⟨hj1, hj2⟩)
    simpa only [sm_ext_add, sm_ext_smul] using this
  · intro j hj
    simp [hzero j hj, hdz j hj]

abbrev SmO (n k ℓ : ℕ) := {j : Fin n // ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ)}

theorem sm_tight (n m : ℕ) (q : ℕ → ℝ) (x : Fin n → ℝ)
    (hext : x ∈ (feasLC n m q).extremePoints ℝ)
    (k ℓ : ℕ) (hk : 1 ≤ k) (hkle : k ≤ ℓ) (hle : ℓ ≤ n)
    (hpos : ∀ j, k ≤ j → j ≤ ℓ → 0 < ext x j)
    (hzero : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0) :
    (ℓ - k + 1) - (m + 1) ≤
      ((Finset.Ioo k ℓ).filter
        (fun j => ext x (j - 1) * ext x (j + 1) = ext x j ^ 2)).card := by
  classical
  by_contra hcon
  push_neg at hcon
  set T := (Finset.Ioo k ℓ).filter (fun j => ext x (j - 1) * ext x (j + 1) = ext x j ^ 2) with hT
  obtain ⟨hxF, hextr⟩ := mem_extremePoints.1 hext
  obtain ⟨k', ℓ', hk', hkl', hle', hmom, hlc', hpos', hzero'⟩ := hxF
  have hz := sm_ext_zero_of_out x k ℓ hk hle hzero
  have hz' := sm_ext_zero_of_out x k' ℓ' hk' hle' hzero'
  have hkk : k' = k := by
    apply le_antisymm
    · by_contra h; exact absurd (hz' k (by omega)) (hpos k le_rfl hkle).ne'
    · by_contra h; exact absurd (hz k' (by omega)) (hpos' k' le_rfl hkl').ne'
  have hll : ℓ' = ℓ := by
    apply le_antisymm
    · by_contra h; exact absurd (hz ℓ' (by omega)) (hpos' ℓ' hkl' le_rfl).ne'
    · by_contra h; exact absurd (hz' ℓ (by omega)) (hpos ℓ hkle le_rfl).ne'
  subst hkk hll
  -- the linear map
  let Φ : (Fin n → ℝ) →ₗ[ℝ] ((Fin (m + 1) → ℝ) × (T → ℝ) × (SmO n k' ℓ' → ℝ)) :=
    { toFun := fun d => (fun i => moment d i.val,
        fun j => ext x (j.val + 1) * ext d (j.val - 1) + ext x (j.val - 1) * ext d (j.val + 1)
          - 2 * ext x j.val * ext d j.val,
        fun o => d o.val)
      map_add' := by
        intro d e
        ext <;> simp [sm_moment_add, sm_ext_add] <;> ring
      map_smul' := by
        intro s d
        ext <;> simp [sm_moment_smul, sm_ext_smul] <;> ring }
  have hcardO : Fintype.card (SmO n k' ℓ') + (ℓ' - k' + 1) ≤ n := by
    have h1 : Fintype.card (SmO n k' ℓ') = n - Fintype.card {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} := by
      have := Fintype.card_subtype_compl (fun j : Fin n => k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ')
      simpa using this
    have h2 : ℓ' - k' + 1 ≤ Fintype.card {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} := by
      have : Fintype.card (Finset.Icc k' ℓ') ≤
          Fintype.card {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} := by
        refine Fintype.card_le_of_injective
          (fun i => (⟨⟨i.1 - 1, by have := Finset.mem_Icc.1 i.2; omega⟩, by
            have := Finset.mem_Icc.1 i.2; simp only; omega⟩ : {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'})) ?_
        intro i1 i2 h
        have h' := congrArg (fun p : {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} => p.1.val) h
        have a1 := Finset.mem_Icc.1 i1.2
        have a2 := Finset.mem_Icc.1 i2.2
        apply Subtype.ext
        simp only at h'
        omega
      have hc : Fintype.card (Finset.Icc k' ℓ') = ℓ' + 1 - k' := by simp
      omega
    have h3 : Fintype.card {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} ≤ n := by
      simpa using Fintype.card_subtype_le (fun j : Fin n => k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ')
    omega
  have hfin : Module.finrank ℝ ((Fin (m + 1) → ℝ) × (T → ℝ) × (SmO n k' ℓ' → ℝ)) <
      Module.finrank ℝ (Fin n → ℝ) := by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Fintype.card_coe]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hfin
  obtain ⟨d, hdker, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hΦ : Φ d = 0 := hdker
  have hdm : ∀ i ≤ m, moment d i = 0 := by
    intro i hi
    have := congrFun (congrArg Prod.fst hΦ) ⟨i, by omega⟩
    simpa [Φ] using this
  have hdz : ∀ j : Fin n, ¬ (k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ') → d j = 0 := by
    intro j hj
    have := congrFun (congrArg (fun p => p.2.2) hΦ) ⟨j, hj⟩
    simpa [Φ] using this
  have hdt : ∀ j, k' < j → j < ℓ' → ext x (j - 1) * ext x (j + 1) = ext x j ^ 2 →
      ext x (j + 1) * ext d (j - 1) + ext x (j - 1) * ext d (j + 1) = 2 * ext x j * ext d j := by
    intro j hj1 hj2 ht
    have hjT : j ∈ T := by rw [hT, Finset.mem_filter, Finset.mem_Ioo]; exact ⟨⟨hj1, hj2⟩, ht⟩
    have := congrFun (congrArg (fun p => p.2.1) hΦ) ⟨j, hjT⟩
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_zero, Prod.fst_zero, Pi.zero_apply] at this
    linarith
  have hev := sm_perturb n m q x d k' ℓ' hk' hkl' hle' hmom hlc' hpos hzero hdm hdz hdt
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  have hp : x + (ε / 2) • d ∈ feasLC n m q := hεb (show dist (ε / 2) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm : x + (-(ε / 2)) • d ∈ feasLC n m q := hεb (show dist (-(ε / 2)) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  have hseg : x ∈ openSegment ℝ (x + (ε / 2) • d) (x + (-(ε / 2)) • d) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    simp
    ring
  have := (hextr _ hp _ hm hseg).1
  have h0 : (ε / 2) • d = 0 := by simpa using this
  rcases smul_eq_zero.1 h0 with h | h
  · linarith
  · exact hd0 h

lemma sm_snoc (a : ℕ → ℝ) (k j ℓ c : ℕ) (hkj : k ≤ j) (hjl : j ≤ ℓ)
    (hpos : ∀ i, k ≤ i → i ≤ ℓ → 0 < a i)
    (htight : ∀ i, j < i → i < ℓ → a (i - 1) * a (i + 1) = a i ^ 2)
    (h : ∃ b : ℕ → ℕ, ∃ α r : ℕ → ℝ, Monotone b ∧ b 0 = k ∧ b (c + 1) = j ∧
      ∀ i < c + 1, 0 < α i ∧ 0 < r i ∧ ∀ t, b i ≤ t → t ≤ b (i + 1) →
        a t = α i * r i ^ (t - b i)) :
    ∃ b : ℕ → ℕ, ∃ α r : ℕ → ℝ, Monotone b ∧ b 0 = k ∧ b (c + 2) = ℓ ∧
      ∀ i < c + 2, 0 < α i ∧ 0 < r i ∧ ∀ t, b i ≤ t → t ≤ b (i + 1) →
        a t = α i * r i ^ (t - b i) := by
  obtain ⟨b, α, r, hmono, hb0, hbc, hpc⟩ := h
  obtain ⟨ρ, hρ, hρt⟩ := ShapeMoment.LogConcave.geometric_of_tight a j ℓ hjl (fun i h1 h2 => hpos i (by omega) h2) htight
  refine ⟨fun i => if i ≤ c + 1 then b i else ℓ, fun i => if i ≤ c then α i else a j,
    fun i => if i ≤ c then r i else ρ, ?_, ?_, ?_, ?_⟩
  · intro i i' hii
    simp only
    have hbl : ∀ t, t ≤ c + 1 → b t ≤ j := fun t ht => hbc ▸ hmono ht
    by_cases h1 : i ≤ c + 1 <;> by_cases h2 : i' ≤ c + 1 <;> simp only [h1, h2, if_true, if_false] <;>
      first | exact hmono hii | (have := hbl i h1; omega) | omega | exact le_rfl
  · simp [hb0]
  · simp
  · intro i hi
    by_cases hic : i ≤ c
    · obtain ⟨h1, h2, h3⟩ := hpc i (by omega)
      simp only [hic, if_true, show i + 1 ≤ c + 1 by omega, show i ≤ c + 1 by omega]
      exact ⟨h1, h2, h3⟩
    · have hi' : i = c + 1 := by omega
      subst hi'
      simp only [show ¬ (c + 1 ≤ c) by omega, if_false, le_refl, if_true, hbc,
        show ¬ (c + 1 + 1 ≤ c + 1) by omega]
      refine ⟨hpos j hkj (by omega), hρ, ?_⟩
      intro t h1 h2
      exact hρt t h1 h2

lemma sm_pieces (a : ℕ → ℝ) (k : ℕ) : ∀ c ℓ, k ≤ ℓ → (∀ j, k ≤ j → j ≤ ℓ → 0 < a j) →
    ((Finset.Ioo k ℓ).filter (fun j => ¬ a (j - 1) * a (j + 1) = a j ^ 2)).card ≤ c →
    ∃ b : ℕ → ℕ, ∃ α r : ℕ → ℝ, Monotone b ∧ b 0 = k ∧ b (c + 1) = ℓ ∧
      ∀ i < c + 1, 0 < α i ∧ 0 < r i ∧ ∀ t, b i ≤ t → t ≤ b (i + 1) →
        a t = α i * r i ^ (t - b i) := by
  intro c
  induction c with
  | zero =>
    intro ℓ hkl hpos hcard
    have hempty : (Finset.Ioo k ℓ).filter (fun j => ¬ a (j - 1) * a (j + 1) = a j ^ 2) = ∅ :=
      Finset.card_eq_zero.1 (by omega)
    have htight : ∀ j, k < j → j < ℓ → a (j - 1) * a (j + 1) = a j ^ 2 := by
      intro j h1 h2
      by_contra hne
      have : j ∈ (Finset.Ioo k ℓ).filter (fun j => ¬ a (j - 1) * a (j + 1) = a j ^ 2) := by
        simp only [Finset.mem_filter, Finset.mem_Ioo]; exact ⟨⟨h1, h2⟩, hne⟩
      rw [hempty] at this; simp at this
    obtain ⟨ρ, hρ, hρt⟩ := ShapeMoment.LogConcave.geometric_of_tight a k ℓ hkl hpos htight
    refine ⟨fun i => if i = 0 then k else ℓ, fun _ => a k, fun _ => ρ, ?_, by simp, by simp, ?_⟩
    · intro i i' hii
      simp only
      split_ifs <;> first | omega | exact le_rfl
    · intro i hi
      have : i = 0 := by omega
      subst this
      refine ⟨hpos k le_rfl hkl, hρ, ?_⟩
      intro t h1 h2
      simp only [if_true, show ¬ (0 + 1 = 0) by omega, if_false] at h1 h2 ⊢
      exact hρt t h1 h2
  | succ c ih =>
    intro ℓ hkl hpos hcard
    set F := (Finset.Ioo k ℓ).filter (fun j => ¬ a (j - 1) * a (j + 1) = a j ^ 2) with hF
    obtain ⟨j, hkj, hjl, hcj, hjt⟩ : ∃ j, k ≤ j ∧ j ≤ ℓ ∧
        ((Finset.Ioo k j).filter (fun i => ¬ a (i - 1) * a (i + 1) = a i ^ 2)).card ≤ c ∧
        (∀ i, j < i → i < ℓ → a (i - 1) * a (i + 1) = a i ^ 2) := by
      by_cases hne : F.Nonempty
      · obtain ⟨jj, hjjF, hjjmax⟩ : ∃ jj ∈ F, ∀ i ∈ F, i ≤ jj :=
          ⟨F.max' hne, F.max'_mem hne, fun i hi => F.le_max' i hi⟩
        have hjj := hjjF
        simp only [hF, Finset.mem_filter, Finset.mem_Ioo] at hjj
        refine ⟨jj, by omega, by omega, ?_, ?_⟩
        · have hsub : (Finset.Ioo k jj).filter (fun i => ¬ a (i - 1) * a (i + 1) = a i ^ 2)
              ⊆ F.erase jj := by
            intro i hi
            simp only [hF, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_erase] at hi ⊢
            refine ⟨by omega, ⟨hi.1.1, by omega⟩, hi.2⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hjjF] at this
          omega
        · intro i h1 h2
          by_contra hn
          have hi : i ∈ F := by
            simp only [hF, Finset.mem_filter, Finset.mem_Ioo]
            exact ⟨⟨by omega, h2⟩, hn⟩
          have := hjjmax i hi
          omega
      · refine ⟨ℓ, hkl, le_rfl, ?_, fun i h1 h2 => by omega⟩
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have : ((Finset.Ioo k ℓ).filter (fun i => ¬ a (i - 1) * a (i + 1) = a i ^ 2)).card = 0 := by
          rw [← hF, hne]; simp
        omega
    have hmid := ih j hkj (fun i h1 h2 => hpos i h1 (by omega)) hcj
    exact sm_snoc a k j ℓ c hkj hjl hpos hjt hmid

lemma sm_cont_ext {n : ℕ} (i : ℕ) : Continuous (fun x : Fin n → ℝ => ext x i) := by
  unfold ext
  by_cases h : 1 ≤ i ∧ i ≤ n
  · simp only [dif_pos h]; exact continuous_apply _
  · simp only [dif_neg h]; exact continuous_const

lemma sm_cont_moment {n : ℕ} (i : ℕ) : Continuous (fun x : Fin n → ℝ => moment x i) := by
  unfold moment
  fun_prop

lemma sm_closed_prime (n m : ℕ) (q : ℕ → ℝ) : IsClosed (feasLCPrime n m q) := by
  have h1 : IsClosed {x : Fin n → ℝ | ∀ i ≤ m, moment x i = q i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (sm_cont_moment i) continuous_const
  have h2 : IsClosed {x : Fin n → ℝ | ∀ j u v : ℕ, 1 < j → j < n → 1 ≤ u → u ≤ j - 1 →
      1 ≤ v → v ≤ n - j → ext x (j - u) ^ v * ext x (j + v) ^ u ≤ ext x j ^ (u + v)} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun u => isClosed_iInter fun v =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_le (((sm_cont_ext _).pow _).mul ((sm_cont_ext _).pow _))
      ((sm_cont_ext _).pow _)
  have h3 : IsClosed {x : Fin n → ℝ | ∀ j, 0 ≤ x j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  exact h1.inter (h2.inter h3)

lemma sm_compact (n m : ℕ) (q : ℕ → ℝ) (hq0 : q 0 = 1) : IsCompact (feasLC n m q) := by
  rw [ShapeMoment.LogConcave.proposition_2_4 n m q hq0]
  have hsub : feasLCPrime n m q ⊆ Set.Icc 0 1 := by
    rintro y ⟨hmom, _, hnn⟩
    have hsum : ∑ j, y j = 1 := by
      have := hmom 0 (Nat.zero_le _)
      simp only [moment, pow_zero, one_mul, hq0] at this
      exact this
    refine ⟨fun j => hnn j, fun j => ?_⟩
    have := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
    simp only [Pi.one_apply]
    linarith
  exact isCompact_Icc.of_isClosed_subset (sm_closed_prime n m q) hsub

lemma sm_exists_ext (n m : ℕ) (q : ℕ → ℝ) (f : Fin n → ℝ) (hq0 : q 0 = 1)
    (hfeas : (feasLC n m q).Nonempty) :
    ∃ x ∈ (feasLC n m q).extremePoints ℝ, IsMaxSol f (feasLC n m q) x := by
  have hc := sm_compact n m q hq0
  have hobj : Continuous (fun y : Fin n → ℝ => ∑ j, f j * y j) := by fun_prop
  obtain ⟨x0, hx0F, hx0⟩ := hc.exists_isMaxOn hfeas hobj.continuousOn
  have hMc : IsCompact (feasLC n m q ∩ {y | ∑ j, f j * y j = ∑ j, f j * x0 j}) :=
    hc.inter_right (isClosed_eq hobj continuous_const)
  have hMne : (feasLC n m q ∩ {y | ∑ j, f j * y j = ∑ j, f j * x0 j}).Nonempty := ⟨x0, hx0F, rfl⟩
  have hS : Continuous (fun y : Fin n → ℝ => ∑ j, y j ^ 2) := by fun_prop
  obtain ⟨z, hzM, hzmax⟩ := hMc.exists_isMaxOn hMne hS.continuousOn
  have hle : ∀ y ∈ feasLC n m q, ∑ j, f j * y j ≤ ∑ j, f j * x0 j := fun y hy => isMaxOn_iff.1 hx0 y hy
  have hzobj : ∑ j, f j * z j = ∑ j, f j * x0 j := hzM.2
  have hext : z ∈ (feasLC n m q).extremePoints ℝ := by
    refine mem_extremePoints.2 ⟨hzM.1, ?_⟩
    intro x1 hx1 x2 hx2 hz
    obtain ⟨a, b, ha, hb, hab, hzeq⟩ := hz
    have hb' : b = 1 - a := by linarith
    have hlin : ∑ j, f j * z j = a * (∑ j, f j * x1 j) + b * (∑ j, f j * x2 j) := by
      rw [← hzeq]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl (fun j _ => by ring)
    have o1 := hle x1 hx1
    have o2 := hle x2 hx2
    have e1 : ∑ j, f j * x1 j = ∑ j, f j * x0 j := by
      by_contra hne
      have : ∑ j, f j * x1 j < ∑ j, f j * x0 j := lt_of_le_of_ne o1 hne
      have hcc : a * ∑ j, f j * x0 j + b * ∑ j, f j * x0 j = ∑ j, f j * x0 j := by
        rw [← add_mul, hab, one_mul]
      nlinarith [mul_pos ha (sub_pos.2 this), mul_nonneg hb.le (sub_nonneg.2 o2)]
    have e2 : ∑ j, f j * x2 j = ∑ j, f j * x0 j := by
      by_contra hne
      have : ∑ j, f j * x2 j < ∑ j, f j * x0 j := lt_of_le_of_ne o2 hne
      have hcc : a * ∑ j, f j * x0 j + b * ∑ j, f j * x0 j = ∑ j, f j * x0 j := by
        rw [← add_mul, hab, one_mul]
      nlinarith [mul_pos hb (sub_pos.2 this), mul_nonneg ha.le (sub_nonneg.2 o1)]
    have s1 : ∑ j, x1 j ^ 2 ≤ ∑ j, z j ^ 2 := isMaxOn_iff.1 hzmax x1 ⟨hx1, e1⟩
    have s2 : ∑ j, x2 j ^ 2 ≤ ∑ j, z j ^ 2 := isMaxOn_iff.1 hzmax x2 ⟨hx2, e2⟩
    have hid : ∑ j, z j ^ 2 = a * ∑ j, x1 j ^ 2 + b * ∑ j, x2 j ^ 2
        - a * b * ∑ j, (x1 j - x2 j) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hj : z j = a * x1 j + b * x2 j := by
        have := congrFun hzeq j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        linarith
      rw [hj, hb']; ring
    have hD : 0 ≤ ∑ j, (x1 j - x2 j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hD0 : ∑ j, (x1 j - x2 j) ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ∑ j, (x1 j - x2 j) ^ 2 := lt_of_le_of_ne hD (Ne.symm hne)
      have hcc : a * ∑ j, z j ^ 2 + b * ∑ j, z j ^ 2 = ∑ j, z j ^ 2 := by
        rw [← add_mul, hab, one_mul]
      nlinarith [mul_pos (mul_pos ha hb) hpos, mul_le_mul_of_nonneg_left s1 ha.le,
        mul_le_mul_of_nonneg_left s2 hb.le]
    have hx12 : x1 = x2 := by
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x1 j - x2 j))).1 hD0 j
        (Finset.mem_univ j)
      nlinarith [sq_nonneg (x1 j - x2 j)]
    subst hx12
    have hzx : z = x1 := by
      rw [← hzeq, ← add_smul, hab, one_smul]
    exact ⟨hzx.symm, hzx.symm⟩
  refine ⟨z, hext, hzM.1, fun y hy => ?_⟩
  rw [hzobj]; exact hle y hy

theorem solution (n m : ℕ) (f : Fin n → ℝ) (q : ℕ → ℝ)
    (hq0 : q 0 = 1) (hfeas : (feasLC n m q).Nonempty) :
    (∃ x ∈ (feasLC n m q).extremePoints ℝ,
      IsMaxSol f (feasLC n m q) x) ∧
    ∀ x ∈ (feasLC n m q).extremePoints ℝ,
      IsMaxSol f (feasLC n m q) x →
      ∃ (k ℓ : ℕ) (breakpoint : Fin (m + 1) → ℕ)
        (α r : Fin m → ℝ),
        1 ≤ k ∧ k ≤ ℓ ∧ ℓ ≤ n ∧
        Monotone breakpoint ∧ breakpoint 0 = k ∧
        breakpoint (Fin.last m) = ℓ ∧
        (∀ j, k ≤ j → j ≤ ℓ → 0 < ext x j) ∧
        (∀ j, (j < k ∨ ℓ < j) → ext x j = 0) ∧
        (∀ i, 0 < α i ∧ 0 < r i) ∧
        (∀ i : Fin m, ∀ j, breakpoint i.castSucc ≤ j →
          j ≤ breakpoint i.succ →
          ext x j = α i * r i ^ (j - breakpoint i.castSucc)) := by
  refine ⟨sm_exists_ext n m q f hq0 hfeas, ?_⟩
  intro x hext _
  obtain ⟨hxF, _⟩ := mem_extremePoints.1 hext
  obtain ⟨k, ℓ, hk, hkl, hln, hmom, hlc, hpos, hzero⟩ := hxF
  have htc := sm_tight n m q x hext k ℓ hk hkl hln hpos hzero
  have hz := sm_ext_zero_of_out x k ℓ hk hln hzero
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Ioo k ℓ)
    (fun j => ext x (j - 1) * ext x (j + 1) = ext x j ^ 2)
  have hIoo : (Finset.Ioo k ℓ).card = ℓ - k - 1 := by simp
  have hzz : ∀ j, (j < k ∨ ℓ < j) → ext x j = 0 := fun j hj => hz j (by omega)
  cases m with
  | zero =>
    have hℓk : ℓ = k := by omega
    subst hℓk
    refine ⟨ℓ, ℓ, fun _ => ℓ, Fin.elim0, Fin.elim0, hk, le_rfl, hln, ?_, rfl, rfl, hpos, hzz,
      fun i => i.elim0, fun i => i.elim0⟩
    intro i i' _; exact le_rfl
  | succ c =>
    obtain ⟨b, α, r, hmono, hb0, hbc, hpc⟩ := sm_pieces (ext x) k c ℓ hkl hpos (by omega)
    refine ⟨k, ℓ, fun i => b i.val, fun i => α i.val, fun i => r i.val, hk, hkl, hln,
      fun i i' h => hmono h, hb0, hbc, hpos, hzz,
      fun i => ⟨(hpc i.val i.2).1, (hpc i.val i.2).2.1⟩, ?_⟩
    intro i j h1 h2
    exact (hpc i.val i.2).2.2 j h1 h2

end
