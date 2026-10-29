-- Prove2me | solution 1 for SyncPrefix.Huffman.wielandt_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:25:49.536464+00:00
-- url     : https://prove2.me/submissions/73c5226d-6430-46fd-821f-0f9ef439fff6

import Definitions.Def_SyncPrefix_Huffman_Constructions
import Definitions.Def_SyncPrefix_Huffman_WielandtReduction
import Theorems.Thm_SyncPrefix_Huffman_wielandt_code
import Theorems.Thm_SyncPrefix_Huffman_composition_decoder
import Theorems.Thm_SyncPrefix_Huffman_wielandtAB_encode_polyTime

open SyncPrefix.Huffman

private lemma run_nil {σ α : Type} (δ : σ → α → σ) (q : σ) : run δ q [] = q := rfl

private lemma run_cons {σ α : Type} (δ : σ → α → σ) (q : σ) (a : α) (w : List α) :
    run δ q (a :: w) = run δ (δ q a) w := rfl

private lemma finite_words_length_le (k B : ℕ) :
    {w : List (Fin k) | w.length ≤ B}.Finite := by
  let S : Finset (List (Fin k)) :=
    (Finset.range (B + 1)).biUnion (fun m =>
      (Finset.univ : Finset (Fin m → Fin k)).image List.ofFn)
  refine S.finite_toSet.subset (fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw
  simp only [S, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨w.length, by omega, fun i => w.get i, List.ofFn_get w⟩

private lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2⁻¹)
  rw [Real.log_inv] at h1
  linarith

private lemma wielandtL_bounds (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ wielandtL k ∧
      2 ^ (wielandtL k - 1) ≤ k - 1 ∧
      k ≤ 2 * 2 ^ (wielandtL k - 1) ∧
      (wielandtL k : ℝ) ≤ 2 * Real.log k + 2 := by
  unfold wielandtL
  set m := Nat.log 2 (k - 1)
  have hk1 : k - 1 ≠ 0 := by omega
  have hpow_le : 2 ^ m ≤ k - 1 := Nat.pow_log_le_self 2 hk1
  have hlt_pow : k - 1 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide) (k - 1)
  have hpow_succ : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  simp only [Nat.add_sub_cancel]
  refine ⟨by omega, hpow_le, by omega, ?_⟩
  have hpow_le_k : 2 ^ m ≤ k := by omega
  have hpow_real : ((2 : ℝ) ^ m) ≤ (k : ℝ) := by exact_mod_cast hpow_le_k
  have hlog_le : Real.log ((2 : ℝ) ^ m) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by positivity) hpow_real
  rw [Real.log_pow] at hlog_le
  have hlog2 := half_le_log_two
  have hm_nonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm_half : (m : ℝ) * (1 / 2) ≤ (m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 hm_nonneg
  push_cast
  linarith

private def dupProj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (b : Fin K) : Fin AH.k :=
  if h : b.val < AH.k then ⟨b.val, h⟩ else ⟨0, by omega⟩

private def dupInj (AH : Automaton) (K : ℕ) (hK : AH.k ≤ K) (a : Fin AH.k) : Fin K :=
  ⟨a.val, Nat.lt_of_lt_of_le a.isLt hK⟩

private lemma dupTransition_eq_proj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k)
    (q : Fin AH.n) (b : Fin K) :
    dupTransition AH K q b = AH.δ q (dupProj AH K hk b) := by
  unfold dupTransition dupProj
  have h0 : 0 < AH.k := by omega
  split_ifs with h
  · rfl
  · rfl

private lemma dupProj_dupInj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (a : Fin AH.k) :
    dupProj AH K hk (dupInj AH K hK a) = a := by
  unfold dupProj dupInj
  simp [a.isLt]

private lemma run_dupTransition (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k)
    (q : Fin AH.n) (y : List (Fin K)) :
    run (dupTransition AH K) q y = run AH.δ q (y.map (dupProj AH K hk)) := by
  induction y generalizing q with
  | nil => rfl
  | cons b y ih =>
    simp only [List.map_cons, run_cons, dupTransition_eq_proj AH K hk]
    exact ih _

private lemma map_dupProj_dupInj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (w : List (Fin AH.k)) :
    (w.map (dupInj AH K hK)).map (dupProj AH K hk) = w := by
  rw [List.map_map]
  have hcomp : dupProj AH K hk ∘ dupInj AH K hK = id := funext (dupProj_dupInj AH K hk hK)
  rw [hcomp, List.map_id]

private lemma run_dupTransition_map_inj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (q : Fin AH.n) (w : List (Fin AH.k)) :
    run (dupTransition AH K) q (w.map (dupInj AH K hK)) = run AH.δ q w := by
  rw [run_dupTransition AH K hk, map_dupProj_dupInj AH K hk hK]

private lemma isFirstReturn_map_dupProj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k)
    {r : Fin AH.n} {y : List (Fin K)} (hy : IsFirstReturn (dupTransition AH K) r y) :
    IsFirstReturn AH.δ r (y.map (dupProj AH K hk)) := by
  rcases hy with ⟨hne, hret, hmin⟩
  refine ⟨by simpa using hne, ?_, ?_⟩
  · rw [← run_dupTransition AH K hk]
    exact hret
  · intro i hi0 hi_lt
    rw [List.length_map] at hi_lt
    rw [← List.map_take, ← run_dupTransition AH K hk]
    exact hmin i hi0 hi_lt

private lemma isHuffmanDecoder_dupTransition (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (hHuff : IsHuffmanDecoder AH.δ) :
    IsHuffmanDecoder (dupTransition AH K) := by
  rcases hHuff with ⟨hSC, r, hfin⟩
  refine ⟨fun q q' => ?_, r, ?_⟩
  · obtain ⟨w, hw⟩ := hSC q q'
    exact ⟨w.map (dupInj AH K hK), by rw [run_dupTransition_map_inj AH K hk hK, hw]⟩
  · let B := hfin.toFinset.sup List.length
    refine (finite_words_length_le K B).subset (fun y hy => ?_)
    simp only [Set.mem_setOf_eq] at hy ⊢
    have hmap : y.map (dupProj AH K hk) ∈ hfin.toFinset :=
      hfin.mem_toFinset.mpr (isFirstReturn_map_dupProj AH K hk hy)
    have hle := Finset.le_sup (f := List.length) hmap
    simpa using hle

private lemma sync_dupTransition (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (hSync : IsSynchronizing AH.δ) :
    IsSynchronizing (dupTransition AH K) ∧ syncLength (dupTransition AH K) = syncLength AH.δ := by
  have hset_eq :
      {ℓ | ∃ y : List (Fin K), y.length = ℓ ∧ IsSyncWord (dupTransition AH K) y} =
        {ℓ | ∃ w : List (Fin AH.k), w.length = ℓ ∧ IsSyncWord AH.δ w} := by
    ext ℓ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, rfl, q, hq⟩
      refine ⟨y.map (dupProj AH K hk), List.length_map .., q, fun q' => ?_⟩
      rw [← run_dupTransition AH K hk]
      exact hq q'
    · rintro ⟨w, rfl, q, hq⟩
      refine ⟨w.map (dupInj AH K hK), List.length_map .., q, fun q' => ?_⟩
      rw [run_dupTransition_map_inj AH K hk hK]
      exact hq q'
  refine ⟨?_, ?_⟩
  · rcases hSync with ⟨w, q, hq⟩
    exact ⟨w.map (dupInj AH K hK), q, fun q' => by
      rw [run_dupTransition_map_inj AH K hk hK]
      exact hq q'⟩
  · unfold syncLength
    rw [hset_eq]

private lemma properPrefixes_wielandtCode_card (L : ℕ) (hL : 1 ≤ L) :
    (properPrefixes (wielandtCode L)).card + 1 = (wielandtCode L).card := by
  set Z := wielandtCode L
  obtain ⟨hMaxZ, hCardZ, -⟩ := wielandt_code L hL
  have hComp := (composition_decoder (fun (_ : Unit) (_ : Fin Z.card) => ()) Z hMaxZ
    (wielandtCodeEquiv L)).1
  simp only [Fintype.card_bool, Fintype.card_prod, Fintype.card_unit, Fintype.card_coe,
    one_mul] at hComp
  have hZ_pos : 0 < Z.card := by
    rw [hCardZ]
    positivity
  have hZ_sub : Z ⊆ allPrefixes Z := by
    intro z hz
    simp only [allPrefixes, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
    exact ⟨z, hz, List.prefix_refl z⟩
  have hnil_all : [] ∈ allPrefixes Z := by
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hZ_pos
    simp only [allPrefixes, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
    exact ⟨z, hz, List.nil_prefix⟩
  have hnil_not_Z : [] ∉ Z := hMaxZ.1.1
  have hpp_eq : properPrefixes Z = allPrefixes Z \ Z := by
    ext p
    simp only [properPrefixes, Finset.mem_insert, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro (rfl | ⟨hp1, hp2⟩)
      · exact ⟨hnil_all, hnil_not_Z⟩
      · exact ⟨hp1, hp2⟩
    · rintro ⟨hp1, hp2⟩
      exact Or.inr ⟨hp1, hp2⟩
  have hcard_sdiff : (properPrefixes Z).card + Z.card = (allPrefixes Z).card := by
    rw [hpp_eq]
    exact Finset.card_sdiff_add_card_eq_card hZ_sub
  omega

private lemma run_reindex {σ₁ σ₂ α₁ α₂ : Type} (δ₁ : σ₁ → α₁ → σ₁)
    (es : σ₁ ≃ σ₂) (ea : α₂ ≃ α₁) (s : σ₂) (w : List α₂) :
    run (fun q a => es (δ₁ (es.symm q) (ea a))) s w =
      es (run δ₁ (es.symm s) (w.map ea)) := by
  induction w generalizing s with
  | nil => simp [run_nil]
  | cons a w ih =>
    simp only [List.map_cons, run_cons]
    rw [ih]
    simp

private lemma isHuffmanDecoder_reindex {σ₁ σ₂ α₁ α₂ : Type} (δ₁ : σ₁ → α₁ → σ₁)
    (es : σ₁ ≃ σ₂) (ea : α₂ ≃ α₁) (hHuff : IsHuffmanDecoder δ₁) :
    IsHuffmanDecoder (fun q a => es (δ₁ (es.symm q) (ea a))) := by
  rcases hHuff with ⟨hSC, r, hfin⟩
  refine ⟨fun s s' => ?_, es r, ?_⟩
  · obtain ⟨w₁, hw₁⟩ := hSC (es.symm s) (es.symm s')
    refine ⟨w₁.map ea.symm, ?_⟩
    rw [run_reindex, List.map_map]
    have hcomp : (ea ∘ ea.symm : α₁ → α₁) = id := funext ea.apply_symm_apply
    rw [hcomp, List.map_id, hw₁, es.apply_symm_apply]
  · refine (hfin.image (List.map ea.symm)).subset (fun w hw => ?_)
    simp only [Set.mem_setOf_eq] at hw
    rcases hw with ⟨hne, hret, hmin⟩
    refine ⟨w.map ea, ⟨by simpa using hne, ?_, ?_⟩, ?_⟩
    · rw [run_reindex, es.symm_apply_apply, es.injective.eq_iff] at hret
      exact hret
    · intro i hi0 hi_lt
      rw [List.length_map] at hi_lt
      have hmin_i := hmin i hi0 hi_lt
      rw [run_reindex, es.symm_apply_apply, Ne, es.injective.eq_iff, List.map_take] at hmin_i
      exact hmin_i
    · rw [List.map_map]
      have hcomp : (ea.symm ∘ ea : α₂ → α₂) = id := funext ea.symm_apply_apply
      rw [hcomp, List.map_id]

private lemma isSynchronizing_reindex {σ₁ σ₂ α₁ α₂ : Type} (δ₁ : σ₁ → α₁ → σ₁)
    (es : σ₁ ≃ σ₂) (ea : α₂ ≃ α₁) (hSync : IsSynchronizing δ₁) :
    IsSynchronizing (fun q a => es (δ₁ (es.symm q) (ea a))) := by
  rcases hSync with ⟨w₁, q, hq⟩
  refine ⟨w₁.map ea.symm, es q, fun s => ?_⟩
  rw [run_reindex, List.map_map]
  have hcomp : (ea ∘ ea.symm : α₁ → α₁) = id := funext ea.apply_symm_apply
  rw [hcomp, List.map_id, hq]

private lemma syncLength_reindex {σ₁ σ₂ α₁ α₂ : Type} (δ₁ : σ₁ → α₁ → σ₁)
    (es : σ₁ ≃ σ₂) (ea : α₂ ≃ α₁) :
    syncLength (fun q a => es (δ₁ (es.symm q) (ea a))) = syncLength δ₁ := by
  have hset_eq :
      {ℓ | ∃ w : List α₂, w.length = ℓ ∧ IsSyncWord (fun q a => es (δ₁ (es.symm q) (ea a))) w} =
        {ℓ | ∃ w₁ : List α₁, w₁.length = ℓ ∧ IsSyncWord δ₁ w₁} := by
    ext ℓ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, rfl, s₀, hs₀⟩
      refine ⟨w.map ea, List.length_map .., es.symm s₀, fun q₁ => ?_⟩
      have h := hs₀ (es q₁)
      rw [run_reindex, es.symm_apply_apply] at h
      exact (es.symm_apply_eq.mpr h.symm).symm
    · rintro ⟨w₁, rfl, q₀, hq₀⟩
      refine ⟨w₁.map ea.symm, List.length_map .., es q₀, fun s => ?_⟩
      rw [run_reindex, List.map_map]
      have hcomp : (ea ∘ ea.symm : α₁ → α₁) = id := funext ea.apply_symm_apply
      rw [hcomp, List.map_id, hq₀]
  unfold syncLength
  rw [hset_eq]

theorem solution (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg_H : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg_H ∧
      ∀ AH : Automaton, IsHuffmanDecoder AH.δ → IsSynchronizing AH.δ → 2 ≤ AH.n → 2 ≤ AH.k →
        ∃ (L : ℕ) (δY : Fin AH.n → Fin (wielandtCode L).card → Fin AH.n)
          (e : Fin (wielandtCode L).card ≃ {z // z ∈ wielandtCode L}) (AB : Automaton),
          1 ≤ L ∧ (L : ℝ) ≤ 2 * Real.log AH.k + 2 ∧
          IsHuffmanDecoder δY ∧ IsSynchronizing δY ∧ syncLength δY = syncLength AH.δ ∧
          AB.k = 2 ∧ AH.n ≤ AB.n ∧ AB.n ≤ 6 * AH.n * AH.k ∧
          (IsHuffmanDecoder (composeDecoder δY (wielandtCode L) e) → IsHuffmanDecoder AB.δ) ∧
          (IsSynchronizing (composeDecoder δY (wielandtCode L) e) → IsSynchronizing AB.δ) ∧
          syncLength AB.δ = syncLength (composeDecoder δY (wielandtCode L) e) ∧
          (Alg_H AH.encode).length = (Alg AB.encode).length / L := by
  obtain ⟨Alg_H, hAlg_H, hAlg_H_spec⟩ := wielandtAB_encode_polyTime Alg hAlg
  refine ⟨Alg_H, hAlg_H, fun AH hHuff hSync hn2 hk2 => ?_⟩
  have ⟨hL1, hpow_le, hk_le_pow, hL_real⟩ := wielandtL_bounds AH.k hk2
  set L := wielandtL AH.k
  obtain ⟨-, hCardZ, -⟩ := wielandt_code L hL1
  have hK : AH.k ≤ (wielandtCode L).card := by
    rw [hCardZ]
    omega
  let δY := dupTransition AH (wielandtCode L).card
  let e := wielandtCodeEquiv L
  let AB := wielandtAB AH
  have hHuffY : IsHuffmanDecoder δY := isHuffmanDecoder_dupTransition AH _ hk2 hK hHuff
  have ⟨hSyncY, hLenY⟩ := sync_dupTransition AH _ hk2 hK hSync
  have hpp_card := properPrefixes_wielandtCode_card L hL1
  have hpp_ge1 : 1 ≤ (properPrefixes (wielandtCode L)).card := by
    have : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
    omega
  have hpp_le : (properPrefixes (wielandtCode L)).card ≤ 6 * AH.k := by
    omega
  refine ⟨L, δY, e, AB, hL1, hL_real, hHuffY, hSyncY, hLenY, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show AH.n ≤ AH.n * (properPrefixes (wielandtCode L)).card
    exact Nat.le_mul_of_pos_right AH.n hpp_ge1
  · show AH.n * (properPrefixes (wielandtCode L)).card ≤ 6 * AH.n * AH.k
    calc AH.n * (properPrefixes (wielandtCode L)).card
        ≤ AH.n * (6 * AH.k) := Nat.mul_le_mul_left AH.n hpp_le
      _ = 6 * AH.n * AH.k := by ring
  · exact isHuffmanDecoder_reindex (composeDecoder δY (wielandtCode L) e)
      (wielandtStateEquiv AH.n L) fin2EquivBool
  · exact isSynchronizing_reindex (composeDecoder δY (wielandtCode L) e)
      (wielandtStateEquiv AH.n L) fin2EquivBool
  · exact syncLength_reindex (composeDecoder δY (wielandtCode L) e)
      (wielandtStateEquiv AH.n L) fin2EquivBool
  · exact hAlg_H_spec AH hHuff hSync hn2 hk2
