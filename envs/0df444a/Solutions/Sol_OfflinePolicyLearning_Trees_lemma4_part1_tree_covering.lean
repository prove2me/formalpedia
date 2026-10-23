-- Prove2me | solution 1 for OfflinePolicyLearning.Trees.lemma4_part1_tree_covering
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T16:09:37.499728+00:00
-- url     : https://prove2.me/submissions/835f357a-360b-4fa3-8d9b-8dd5ba8a4beb

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Trees_Setting

set_option autoImplicit false

namespace D582Cover

open OfflinePolicyLearning.Trees

/-- Threshold quantization: finitely many thresholds approximate every threshold up to
`δ * |I|` misrouted points. -/
lemma thresh_grid {ι : Type*} (I : Finset ι) (v : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : Finset ℝ, B.card ≤ ⌊1 / δ⌋₊ + 1 ∧ ∀ b : ℝ, ∃ b' ∈ B,
      ((I.filter fun i => ¬ ((v i < b) ↔ (v i < b'))).card : ℝ) ≤ δ * I.card := by
  classical
  let cnt : ℝ → ℕ := fun b => (I.filter fun i => v i < b).card
  let bucket : ℝ → ℕ := fun b => ⌊(cnt b : ℝ) / (δ * I.card)⌋₊
  have hcntle : ∀ b, (cnt b : ℝ) ≤ I.card := fun b => by
    exact_mod_cast Finset.card_filter_le _ _
  have hbk : ∀ b, bucket b ≤ ⌊1 / δ⌋₊ := by
    intro b
    apply Nat.floor_le_floor
    rcases Nat.eq_zero_or_pos I.card with h0 | hpos
    · simp [h0]; positivity
    · have hpos' : (0:ℝ) < I.card := by exact_mod_cast hpos
      rw [div_le_div_iff₀ (by positivity) hδ]
      nlinarith [hcntle b]
  -- misrouted count for b ≤ b'
  have hmis : ∀ b b' : ℝ, b ≤ b' →
      (I.filter fun i => ¬ ((v i < b) ↔ (v i < b'))).card + cnt b ≤ cnt b' := by
    intro b b' hbb
    have hsub1 : (I.filter fun i => v i < b) ⊆ (I.filter fun i => v i < b') := by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, lt_of_lt_of_le hi.2 hbb⟩
    have hsub2 : (I.filter fun i => ¬ ((v i < b) ↔ (v i < b'))) ⊆
        (I.filter fun i => v i < b') \ (I.filter fun i => v i < b) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_sdiff] at hi ⊢
      obtain ⟨hI, hne⟩ := hi
      by_cases h1 : v i < b
      · exact absurd ⟨fun _ => lt_of_lt_of_le h1 hbb, fun _ => h1⟩ hne
      · by_cases h2 : v i < b'
        · exact ⟨⟨hI, h2⟩, fun h => h1 h.2⟩
        · exact absurd ⟨fun h => absurd h h1, fun h => absurd h h2⟩ hne
    have := Finset.card_le_card hsub2
    have h3 := Finset.card_sdiff_add_card_eq_card hsub1
    show _ + (I.filter fun i => v i < b).card ≤ (I.filter fun i => v i < b').card
    omega
  have hmisR : ∀ b b' : ℝ,
      ((I.filter fun i => ¬ ((v i < b) ↔ (v i < b'))).card : ℝ) ≤ |(cnt b : ℝ) - cnt b'| := by
    intro b b'
    rcases le_total b b' with h | h
    · have := hmis b b' h
      have h' : ((I.filter fun i => ¬ ((v i < b) ↔ (v i < b'))).card : ℝ) + cnt b ≤ cnt b' := by
        exact_mod_cast this
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have := hmis b' b h
      have hsym : (I.filter fun i => ¬ ((v i < b) ↔ (v i < b'))) =
          (I.filter fun i => ¬ ((v i < b') ↔ (v i < b))) := by
        apply Finset.filter_congr
        intro i _
        exact not_congr Iff.comm
      have h' : ((I.filter fun i => ¬ ((v i < b') ↔ (v i < b))).card : ℝ) + cnt b' ≤ cnt b := by
        exact_mod_cast this
      rw [hsym, abs_of_nonneg (by linarith)]
      linarith
  let rep : ℕ → ℝ := fun q => if h : ∃ b, bucket b = q then h.choose else 0
  refine ⟨(Finset.range (⌊1 / δ⌋₊ + 1)).image rep, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro b
    have hex : ∃ b0, bucket b0 = bucket b := ⟨b, rfl⟩
    refine ⟨rep (bucket b), Finset.mem_image.mpr ⟨bucket b, by
      simp only [Finset.mem_range]; exact Nat.lt_succ_of_le (hbk b), rfl⟩, ?_⟩
    have hrep : rep (bucket b) = hex.choose := by simp only [rep, dif_pos hex]
    have hb' : bucket (rep (bucket b)) = bucket b := by rw [hrep]; exact hex.choose_spec
    refine (hmisR b (rep (bucket b))).trans ?_
    set b' := rep (bucket b)
    rcases Nat.eq_zero_or_pos I.card with h0 | hpos
    · have h1 : cnt b = 0 := by
        have := Finset.card_filter_le I (fun i => v i < b); simp only [cnt]; omega
      have h2 : cnt b' = 0 := by
        have := Finset.card_filter_le I (fun i => v i < b'); simp only [cnt]; omega
      simp [h1, h2]; positivity
    · have hpos' : (0:ℝ) < δ * I.card := by
        have : (0:ℝ) < I.card := by exact_mod_cast hpos
        positivity
      have hx0 : (0:ℝ) ≤ (cnt b : ℝ) / (δ * I.card) := by positivity
      have hy0 : (0:ℝ) ≤ (cnt b' : ℝ) / (δ * I.card) := by positivity
      have e1 := Nat.lt_floor_add_one ((cnt b : ℝ) / (δ * I.card))
      have e2 := Nat.lt_floor_add_one ((cnt b' : ℝ) / (δ * I.card))
      have f1 := Nat.floor_le hx0
      have f2 := Nat.floor_le hy0
      have hb'' : ⌊(cnt b' : ℝ) / (δ * I.card)⌋₊ = ⌊(cnt b : ℝ) / (δ * I.card)⌋₊ := hb'
      have hbk' : (⌊(cnt b' : ℝ) / (δ * I.card)⌋₊ : ℝ) = (⌊(cnt b : ℝ) / (δ * I.card)⌋₊ : ℝ) := by
        rw [hb'']
      have hlt : |(cnt b : ℝ) / (δ * I.card) - (cnt b' : ℝ) / (δ * I.card)| < 1 := by
        rw [abs_lt]; constructor <;> linarith
      rw [← sub_div, abs_div, abs_of_pos hpos', div_lt_one hpos'] at hlt
      exact hlt.le

/-- Bound on the size of the cover at depth `n + 1`. -/
def Kb (A d : ℕ) : ℕ → ℕ
  | 0 => d
  | n + 1 => A * Kb A d n ^ 2

lemma log_Kb (A d : ℕ) (hA : 1 ≤ A) (hd : 1 ≤ d) : ∀ n : ℕ, 0 < Kb A d n ∧
    Real.log (Kb A d n : ℝ) ≤ ((2:ℝ) ^ n - 1) * Real.log A + (2:ℝ) ^ n * Real.log d
  | 0 => ⟨by simp only [Kb]; omega, by simp [Kb]⟩
  | n + 1 => by
    obtain ⟨hpos, hlog⟩ := log_Kb A d hA hd n
    refine ⟨by simp only [Kb]; positivity, ?_⟩
    have hA' : (0:ℝ) < A := by exact_mod_cast hA
    have hK' : (0:ℝ) < Kb A d n := by exact_mod_cast hpos
    simp only [Kb]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, pow_succ]
    push_cast
    nlinarith [hlog]

/-- The data-dependent cover of depth-`n+1` trees on the points indexed by `I`. -/
lemma cover_ind {ι : Type*} (p d : ℕ) (x : ι → (Fin p → ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ n : ℕ, ∀ I : Finset ι, ∃ C : Finset (DTree p d (n + 1)),
      C.card ≤ Kb (p * (⌊1 / δ⌋₊ + 1)) d n ∧
      ∀ T : DTree p d (n + 1), ∃ c ∈ C,
        ((I.filter fun i => T.eval (x i) ≠ c.eval (x i)).card : ℝ) ≤ n * δ * I.card := by
  classical
  intro n
  induction n with
  | zero =>
    intro I
    refine ⟨Finset.univ.image (fun a => DTree.leaf a), ?_, ?_⟩
    · simp only [Kb]
      exact Finset.card_image_le.trans (by simp)
    · intro T
      rcases T with ⟨a⟩ | ⟨j, b, l, r⟩
      · refine ⟨DTree.leaf a, by simp, ?_⟩
        simp
      · cases l
  | succ n ih =>
    choose Cov hCovCard hCov using ih
    intro I
    have hB := fun j : Fin p => thresh_grid I (fun i => x i j) δ hδ
    choose B hBcard hB using hB
    let Il : Fin p → ℝ → Finset ι := fun j b => I.filter fun i => x i j < b
    let Ir : Fin p → ℝ → Finset ι := fun j b => I.filter fun i => ¬ x i j < b
    let F : Fin p → ℝ → Finset (DTree p d (n + 1 + 1)) := fun j b =>
      ((Cov (Il j b)) ×ˢ (Cov (Ir j b))).image (fun q => DTree.node j b q.1 q.2)
    let G : Fin p → Finset (DTree p d (n + 1 + 1)) := fun j => (B j).biUnion (F j)
    refine ⟨Finset.univ.biUnion G, ?_, ?_⟩
    · have hF : ∀ j b, (F j b).card ≤ Kb (p * (⌊1 / δ⌋₊ + 1)) d n ^ 2 := by
        intro j b
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_product, sq]
        exact Nat.mul_le_mul (hCovCard _) (hCovCard _)
      have hG : ∀ j, (G j).card ≤ (⌊1 / δ⌋₊ + 1) * Kb (p * (⌊1 / δ⌋₊ + 1)) d n ^ 2 := by
        intro j
        refine Finset.card_biUnion_le.trans ?_
        refine (Finset.sum_le_sum (fun b _ => hF j b)).trans ?_
        rw [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (hBcard j)
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum (fun j _ => hG j)).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      simp only [Kb]
      ring_nf
      exact le_refl _
    · intro T
      rcases T with _ | ⟨j, b, l, r⟩
      obtain ⟨b', hb'B, hmis⟩ := hB j b
      obtain ⟨cl, hclC, hcl⟩ := hCov (Il j b') l
      obtain ⟨cr, hcrC, hcr⟩ := hCov (Ir j b') r
      refine ⟨DTree.node j b' cl cr, ?_, ?_⟩
      · refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
        refine Finset.mem_biUnion.mpr ⟨b', hb'B, ?_⟩
        exact Finset.mem_image.mpr ⟨(cl, cr), Finset.mem_product.mpr ⟨hclC, hcrC⟩, rfl⟩
      · let M := I.filter fun i => ¬ ((x i j < b) ↔ (x i j < b'))
        let Dl := (Il j b').filter fun i => l.eval (x i) ≠ cl.eval (x i)
        let Dr := (Ir j b').filter fun i => r.eval (x i) ≠ cr.eval (x i)
        have hsub : (I.filter fun i =>
            (DTree.node j b l r).eval (x i) ≠ (DTree.node j b' cl cr).eval (x i)) ⊆
            M ∪ Dl ∪ Dr := by
          intro i hi
          rw [Finset.mem_filter] at hi
          obtain ⟨hI, hne⟩ := hi
          simp only [DTree.eval] at hne
          simp only [Finset.mem_union, Finset.mem_filter, M, Dl, Dr, Il, Ir]
          by_cases h1 : x i j < b <;> by_cases h2 : x i j < b'
          · simp only [h1, h2, if_true] at hne
            exact Or.inl (Or.inr ⟨⟨hI, h2⟩, hne⟩)
          · exact Or.inl (Or.inl ⟨hI, fun h => h2 (h.mp h1)⟩)
          · exact Or.inl (Or.inl ⟨hI, fun h => h1 (h.mpr h2)⟩)
          · simp only [h1, h2, if_false] at hne
            exact Or.inr ⟨⟨hI, h2⟩, hne⟩
        have hcard := Finset.card_le_card hsub
        have hu1 := Finset.card_union_le (M ∪ Dl) Dr
        have hu2 := Finset.card_union_le M Dl
        have hsplit : (Il j b').card + (Ir j b').card = I.card :=
          Finset.card_filter_add_card_filter_not _
        have hsplitR : ((Il j b').card : ℝ) + (Ir j b').card = I.card := by exact_mod_cast hsplit
        have hcR : ((I.filter fun i =>
            (DTree.node j b l r).eval (x i) ≠ (DTree.node j b' cl cr).eval (x i)).card : ℝ)
            ≤ (M.card : ℝ) + Dl.card + Dr.card := by
          have : (I.filter fun i =>
            (DTree.node j b l r).eval (x i) ≠ (DTree.node j b' cl cr).eval (x i)).card
            ≤ M.card + Dl.card + Dr.card := by omega
          exact_mod_cast this
        have hn : (0:ℝ) ≤ n := by positivity
        push_cast
        calc _ ≤ (M.card : ℝ) + Dl.card + Dr.card := hcR
          _ ≤ δ * I.card + n * δ * (Il j b').card + n * δ * (Ir j b').card := by
              have := hcl; have := hcr; have := hmis
              linarith
          _ = (n + 1) * δ * I.card := by rw [← hsplitR]; ring

end D582Cover

open D582Cover in
open OfflinePolicyLearning.Trees in
theorem solution (p d L : ℕ) (hp : 1 ≤ p) (hd : 1 ≤ d) (hL : 1 ≤ L) (ε : ℝ)
    (hε : 0 < ε) :
    OfflinePolicyLearning.Regret.hammingCoverNum ε (treePolicies p d L) ≠ ⊤ ∧
      Real.log ((OfflinePolicyLearning.Regret.hammingCoverNum ε (treePolicies p d L)).toNat : ℝ) ≤
        (2 ^ L - 1 : ℝ) * Real.log p + (2 : ℝ) ^ L * Real.log d +
          (2 ^ L - 1 : ℝ) * Real.log (L / ε + 1) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  set δ : ℝ := ε / ((n + 1 : ℕ) : ℝ) with hδdef
  have hδ : 0 < δ := by positivity
  set N := ⌊1 / δ⌋₊ with hN
  set A := p * (N + 1) with hAdef
  have hA : 1 ≤ A := by
    have : 1 ≤ N + 1 := by omega
    calc 1 = 1 * 1 := by ring
      _ ≤ p * (N + 1) := Nat.mul_le_mul hp this
  have hbound : ∀ (m : ℕ) (_ : 1 ≤ m) (x : Fin m → (Fin p → ℝ)),
      OfflinePolicyLearning.Regret.hammingCoverNumOn ε (treePolicies p d (n + 1)) x ≤ Kb A d n := by
    intro m hm x
    obtain ⟨C, hCcard, hC⟩ := cover_ind p d x δ hδ n Finset.univ
    refine (Nat.sInf_le ?_).trans hCcard
    refine ⟨fun k => (C.equivFin.symm k).1.eval, fun k => ⟨_, rfl⟩, ?_⟩
    rintro π ⟨T, rfl⟩
    obtain ⟨c0, hc0, hT⟩ := hC T
    refine ⟨C.equivFin ⟨c0, hc0⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    unfold OfflinePolicyLearning.Regret.hammingDist
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    rw [div_le_iff₀ hm']
    have hcardu : ((Finset.univ : Finset (Fin m)).card : ℝ) = m := by simp
    rw [hcardu] at hT
    have hnδ : (n : ℝ) * δ ≤ ε := by
      rw [hδdef]
      push_cast
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ (n : ℝ) * δ * m := by convert hT using 3
      _ ≤ ε * m := by nlinarith
  have hle : OfflinePolicyLearning.Regret.hammingCoverNum ε (treePolicies p d (n + 1))
      ≤ (Kb A d n : ℕ∞) := by
    unfold OfflinePolicyLearning.Regret.hammingCoverNum
    refine iSup_le fun m => iSup_le fun hm => iSup_le fun x => ?_
    exact_mod_cast hbound m hm x
  have hne : OfflinePolicyLearning.Regret.hammingCoverNum ε (treePolicies p d (n + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
  refine ⟨hne, ?_⟩
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk, ENat.toNat_natCast]
  have hkle : k ≤ Kb A d n := by
    have := hle; rw [← hk] at this; exact_mod_cast this
  obtain ⟨hKpos, hKlog⟩ := log_Kb A d hA hd n
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hp'
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd'
  have hN1 : (1:ℝ) ≤ (N : ℝ) + 1 := by
    have : (0:ℝ) ≤ N := by positivity
    linarith
  have hNle : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / ε := by
    have h1 : (N : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
    have h2 : 1 / δ = ((n + 1 : ℕ) : ℝ) / ε := by rw [hδdef, one_div_div]
    linarith
  have hG : Real.log ((N : ℝ) + 1) ≤ Real.log (((n + 1 : ℕ) : ℝ) / ε + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hG0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg hN1
  have hlogA : Real.log (A : ℝ) = Real.log p + Real.log ((N : ℝ) + 1) := by
    rw [hAdef]; push_cast
    exact Real.log_mul (by positivity) (by positivity)
  have ht : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hlogk : Real.log (k : ℝ) ≤ Real.log (Kb A d n : ℝ) := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast hKpos)
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hkle)
  rw [hlogA] at hKlog
  have hpow : (2:ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [hpow]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hG), mul_nonneg (by linarith : (0:ℝ) ≤ 2 ^ n) hlp,
    mul_nonneg (by linarith : (0:ℝ) ≤ 2 ^ n) hld, mul_nonneg (by linarith : (0:ℝ) ≤ 2 ^ n) hG0,
    mul_nonneg (sub_nonneg.mpr ht) hG0]
