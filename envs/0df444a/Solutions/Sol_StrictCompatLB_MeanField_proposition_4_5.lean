-- Prove2me | solution 1 for StrictCompatLB.MeanField.proposition_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:44:10.712757+00:00
-- url     : https://prove2.me/submissions/ff61db26-2d94-41c8-a6f0-8fe28878c8e2

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Theorems.Thm_StrictCompatLB_MeanField_lemma_F_1

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.P45

open StrictCompatLB.MeanField

/-- The sets `U_j = {v : z_v = j}` (`j < i₀`) and `U_{i₀} = {v : z_v ≥ i₀}`. -/
def Uset {N : ℕ} (z : Fin N → ℕ) (i₀ j : ℕ) : Finset (Fin N) :=
  if j < i₀ then univ.filter (fun v => z v = j) else univ.filter (fun v => i₀ ≤ z v)

lemma card_ge_eq_sum {N : ℕ} (s : Finset (Fin N)) (z : Fin N → ℕ) (i₀ L : ℕ)
    (hL : ∀ v, z v < L) :
    (s.filter (fun v => i₀ ≤ z v)).card = ∑ i ∈ Ico i₀ L, (s.filter (fun v => z v = i)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := z) (t := Ico i₀ L)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [mem_Ico] at hi
    congr 1
    ext v; simp only [mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  · intro v hv
    simp only [coe_filter, Set.mem_setOf_eq] at hv
    simp only [coe_Ico, Set.mem_Ico]
    exact ⟨hv.2, hL v⟩

/-- Deterministic core of Proposition 4.5: a dispatcher whose local distribution is close to the
global one on each of the `i₀ + 1` sets `U_j` is `ε`-good, provided the tail `q_{i₀}` is small. -/
lemma good_of_close (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (hN : 1 ≤ N)
    (z : Fin N → ℕ) (w : Fin (M N)) (ε η : ℝ) (i₀ : ℕ) (hη0 : 0 ≤ η)
    (hη : ((i₀ : ℝ) + 1) * η ≤ ε / 4) (hq : occ z i₀ < ε / 4)
    (hclose : ∀ j ∈ range (i₀ + 1),
      |((nbrW M G N w ∩ Uset z i₀ j).card : ℝ) / ((nbrW M G N w).card : ℝ) -
        ((Uset z i₀ j).card : ℝ) / (N : ℝ)| < η) :
    PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w) < ENNReal.ofReal ε := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  set L := maxLen z + 1 + i₀ with hLdef
  have hzL : ∀ v, z v < L := fun v => by
    have : z v ≤ maxLen z := Finset.le_sup (f := z) (mem_univ v)
    omega
  set nb := nbrW M G N w
  set a : ℕ → ℝ := fun i => (((nb.filter (fun v => z v = i)).card : ℝ)) / (nb.card : ℝ)
  set b : ℕ → ℝ := fun i => (((univ.filter (fun v => z v = i)).card : ℝ)) / (N : ℝ)
  have hgeqd : geqd z = b := rfl
  have hleqd : leqd M G N z w = a := rfl
  have ha0 : ∀ i, 0 ≤ a i := fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hb0 : ∀ i, 0 ≤ b i := fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hzero : ∀ i, L ≤ i → a i = 0 ∧ b i = 0 := by
    intro i hi
    have e : ∀ s : Finset (Fin N), s.filter (fun v => z v = i) = ∅ := by
      intro s; rw [Finset.filter_eq_empty_iff]; intro v _ h; have := hzL v; omega
    simp [a, b, e]
  rw [hgeqd, hleqd]
  unfold PowerOfDUniversality.Fluid.l1dist
  rw [tsum_eq_sum (s := range L) (fun i hi => by
    simp only [mem_range, not_lt] at hi
    obtain ⟨h1, h2⟩ := hzero i hi
    rw [h1, h2]; simp)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  apply (ENNReal.ofReal_lt_ofReal_iff (by
    have : 0 ≤ occ z i₀ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith)).mpr
  have hiL : i₀ ≤ L := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hiL]
  -- the low levels
  have hlow : ∑ i ∈ range i₀, |b i - a i| ≤ i₀ * η := by
    calc ∑ i ∈ range i₀, |b i - a i| ≤ ∑ i ∈ range i₀, η := by
          apply Finset.sum_le_sum; intro i hi
          have hc := hclose i (by simp at hi ⊢; omega)
          have hU : Uset z i₀ i = univ.filter (fun v => z v = i) := by
            simp [Uset, show i < i₀ by simpa using hi]
          rw [hU, Finset.inter_filter, Finset.inter_univ] at hc
          rw [abs_sub_comm]; exact hc.le
      _ = i₀ * η := by simp
  -- the high levels
  have hhigh : ∑ i ∈ Ico i₀ L, |b i - a i| ≤ 2 * occ z i₀ + η := by
    have hU : Uset z i₀ i₀ = univ.filter (fun v => i₀ ≤ z v) := by simp [Uset]
    have hc := hclose i₀ (by simp)
    rw [hU, Finset.inter_filter, Finset.inter_univ] at hc
    have hsb : ∑ i ∈ Ico i₀ L, b i = ((univ.filter (fun v => i₀ ≤ z v)).card : ℝ) / N := by
      simp only [b]
      rw [← Finset.sum_div, card_ge_eq_sum univ z i₀ L hzL]; push_cast; rfl
    have hsa : ∑ i ∈ Ico i₀ L, a i = ((nb.filter (fun v => i₀ ≤ z v)).card : ℝ) / nb.card := by
      simp only [a]
      rw [← Finset.sum_div, card_ge_eq_sum nb z i₀ L hzL]; push_cast; rfl
    have hocc : occ z i₀ = ((univ.filter (fun v => i₀ ≤ z v)).card : ℝ) / N := rfl
    calc ∑ i ∈ Ico i₀ L, |b i - a i| ≤ ∑ i ∈ Ico i₀ L, (b i + a i) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_le]; constructor <;> linarith [ha0 i, hb0 i]
      _ = ∑ i ∈ Ico i₀ L, b i + ∑ i ∈ Ico i₀ L, a i := Finset.sum_add_distrib
      _ ≤ _ := by
          rw [hsb, hsa, ← hocc]
          have := (abs_lt.mp hc).2
          linarith
  have : (i₀ : ℝ) * η + η ≤ ε / 4 := by linarith
  have hocc0 : 0 ≤ occ z i₀ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

lemma badCount_le (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (hN : 1 ≤ N)
    (z : Fin N → ℕ) (ε η : ℝ) (i₀ : ℕ) (hη0 : 0 ≤ η)
    (hη : ((i₀ : ℝ) + 1) * η ≤ ε / 4) (hq : occ z i₀ < ε / 4) (D : ℝ)
    (hsp : ∀ U : Finset (Fin N), (((Finset.univ.filter (fun w : Fin (M N) =>
        η ≤ |((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - (U.card : ℝ) / (N : ℝ)|)).card : ℕ) : ℝ) ≤ D) :
    (badCount M G N ε z : ℝ) ≤ ((i₀ : ℝ) + 1) * D := by
  classical
  have hsub : univ.filter (fun w : Fin (M N) =>
      ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w)) ⊆
      (range (i₀ + 1)).biUnion (fun j => univ.filter (fun w : Fin (M N) =>
        η ≤ |((nbrW M G N w ∩ Uset z i₀ j).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - ((Uset z i₀ j).card : ℝ) / (N : ℝ)|)) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    by_contra hcon
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, not_exists, not_and, not_le] at hcon
    have := good_of_close M G N hN z w ε η i₀ hη0 hη hq hcon
    exact absurd hw (not_le.mpr this)
  unfold badCount
  calc ((univ.filter (fun w : Fin (M N) =>
        ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w))).card : ℝ)
      ≤ (((range (i₀ + 1)).biUnion (fun j => univ.filter (fun w : Fin (M N) =>
        η ≤ |((nbrW M G N w ∩ Uset z i₀ j).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - ((Uset z i₀ j).card : ℝ) / (N : ℝ)|))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ j ∈ range (i₀ + 1), ((univ.filter (fun w : Fin (M N) =>
        η ≤ |((nbrW M G N w ∩ Uset z i₀ j).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - ((Uset z i₀ j).card : ℝ) / (N : ℝ)|)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ j ∈ range (i₀ + 1), D := Finset.sum_le_sum (fun j _ => hsp _)
    _ = ((i₀ : ℝ) + 1) * D := by simp

end StrictCompatLB.MeanField.P45

open StrictCompatLB.MeanField StrictCompatLB.MeanField.P45 in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsparse : IsPropSparse M G)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hroute : ∀ N, 1 ≤ N → IsRoutingRule M G N (route N))
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N)) :
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ T : ℝ, 0 ≤ T →
      Tendsto (fun N => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          δ * (M N : ℝ) ≤ (badCount M G N ε (statePath (Y N) (τ N) ω t) : ℝ)})
        atTop (𝓝 0) := by
  intro ε hε δ hδ T hT
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  by_cases htop : e = ⊤
  · exact Eventually.of_forall (fun N => by rw [htop]; exact le_top)
  have he' : 0 < e.toReal := ENNReal.toReal_pos he.ne' htop
  obtain ⟨i₀, hi₀, N₁, hN₁, hF⟩ := lemma_F_1 lam hlam0 hlam1 M hM G route hroute z₀ q₀ hq₀ hinit
    Ω P Y τ hproc (ε / 4) (by positivity) e.toReal he' (T + 1) (by linarith)
  set η := ε / (4 * ((i₀ : ℝ) + 1)) with hηdef
  have hη0 : 0 < η := by positivity
  have hη : ((i₀ : ℝ) + 1) * η ≤ ε / 4 := by
    rw [hηdef]; apply le_of_eq; field_simp
  obtain ⟨Ns, hNs⟩ := hsparse η hη0 (δ / (2 * ((i₀ : ℝ) + 1))) (by positivity)
  rw [eventually_atTop]
  refine ⟨max (max N₁ Ns) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hMp : (0 : ℝ) < M N := by exact_mod_cast hM N
  have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
      δ * (M N : ℝ) ≤ (badCount M G N ε (statePath (Y N) (τ N) ω t) : ℝ)} ⊆
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) (T + 1), ε / 4 ≤ occPath (Y N) (τ N) ω t i₀} := by
    rintro ω ⟨t, ht, hbad⟩
    refine ⟨t, ⟨ht.1, by linarith [ht.2]⟩, ?_⟩
    by_contra hlt
    push Not at hlt
    have hle := badCount_le M G N hN1 (statePath (Y N) (τ N) ω t) ε η i₀ hη0.le hη hlt
      (δ / (2 * ((i₀ : ℝ) + 1)) * (M N : ℝ))
      (hNs N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN))
    have : ((i₀ : ℝ) + 1) * (δ / (2 * ((i₀ : ℝ) + 1)) * (M N : ℝ)) = δ * M N / 2 := by
      field_simp
    rw [this] at hle
    have : δ * (M N : ℝ) / 2 < δ * M N := by
      have : 0 < δ * (M N : ℝ) := by positivity
      linarith
    linarith
  calc P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
        δ * (M N : ℝ) ≤ (badCount M G N ε (statePath (Y N) (τ N) ω t) : ℝ)}
      ≤ P {ω | ∃ t ∈ Set.Icc (0 : ℝ) (T + 1), ε / 4 ≤ occPath (Y N) (τ N) ω t i₀} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal e.toReal :=
        (hF N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)).le
    _ = e := ENNReal.ofReal_toReal htop
