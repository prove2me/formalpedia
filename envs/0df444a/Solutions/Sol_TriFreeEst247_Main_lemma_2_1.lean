-- Prove2me | solution 1 for TriFreeEst247.Main.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:56:53.894502+00:00
-- url     : https://prove2.me/submissions/51fec570-d7f6-496a-9ab8-17431b41c56b

import Definitions.Def_TriFreeEst247_Main_Score
open TriFreeEst247.Main
open scoped ENNReal symmDiff
set_option maxHeartbeats 1200000

private theorem empty_free {n : ℕ} : triangleFree (⊥ : Graph n) := by
  exact SimpleGraph.cliqueFree_bot (by decide)

private theorem dist_bound {n : ℕ} (G H : Graph n) (h : triangleFree H) :
    distance G ≤ ((edges G ∆ edges H).card : ℝ) / (n : ℝ)^2 := by
  unfold distance
  apply csInf_le _ (show _ ∈ {r : ℝ | ∃ K : Graph n, triangleFree K ∧ r = ((edges G ∆ edges K).card : ℝ) / (n : ℝ)^2} from ⟨H,h,rfl⟩)
  refine ⟨0, ?_⟩
  rintro x ⟨K,_,rfl⟩
  positivity

private theorem dist_nonempty {n : ℕ} (G : Graph n) :
    Set.Nonempty {r : ℝ | ∃ H : Graph n, triangleFree H ∧
        r = ((edges G ∆ edges H).card : ℝ) / (n : ℝ)^2} :=
  ⟨_,⊥,empty_free,rfl⟩

private theorem dist_le_one {n : ℕ} (hn : 1 ≤ n) (G : Graph n) : distance G ≤ 1 := by
  classical
  have h := dist_bound G ⊥ empty_free
  have hcnt : (edges G).card ≤ n.choose 2 := by
    simpa [edges] using G.card_edgeFinset_le_card_choose_two
  have hc : ((edges G).card : ℝ) ≤ (n : ℝ) * (n-1)/2 := by
    rw [← Nat.cast_choose_two]; exact_mod_cast hcnt
  have hz : edges (⊥ : Graph n) = ∅ := by simp [edges]
  rw [hz] at h
  simp [Finset.symmDiff_def] at h
  apply h.trans
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)^2)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n:ℝ)]

private theorem mem_edges {n : ℕ} (H : Graph n) (e : Sym2 (Fin n)) :
    e ∈ edges H ↔ e ∈ H.edgeSet := by classical simp [edges]

private theorem edges_back {n : ℕ} (G : Graph n) {F : EdgeSet n} (hF : F ⊆ edges G) :
    edges (edgeGraph F) = F := by
  classical
  ext e
  rw [mem_edges, edgeGraph, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff]
  constructor
  · exact And.left
  · intro he
    have hG : e ∈ edges G := hF he
    have hed : e ∈ G.edgeSet := by simpa [edges] using hG
    exact ⟨he, SimpleGraph.not_isDiag_of_mem_edgeSet _ hed⟩

private theorem cost_nonneg {n : ℕ} (G : Graph n) (lam : ℝ) (hl : 0 ≤ lam) (D : EdgeSet n) :
    0 ≤ score G lam D := by unfold score edgeDensity triangleDensity; positivity

private theorem residual_distance {n : ℕ} (G : Graph n) (D : EdgeSet n)
    (hD : D ⊆ edges G) :
    distance G ≤ edgeDensity D + distance (edgeGraph (edges G \ D)) := by
  classical
  let H := edgeGraph (edges G \ D)
  have hb : edges H = edges G \ D := edges_back G Finset.sdiff_subset
  rw [← sub_le_iff_le_add']
  apply le_csInf (dist_nonempty H)
  rintro t ⟨K,hK,rfl⟩
  have hi : edges G ∆ edges K ⊆ D ∪ (edges H ∆ edges K) := by
    rw [hb]
    intro x hx
    have ht := Finset.mem_symmDiff.mp hx
    simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_sdiff]
    tauto
  have hc := (Finset.card_le_card hi).trans (Finset.card_union_le _ _)
  have hc' : ((edges G ∆ edges K).card : ℝ) ≤ D.card + ((edges H ∆ edges K).card : ℝ) := by
    exact_mod_cast hc
  have hb' := div_le_div_of_nonneg_right hc' (sq_nonneg (n:ℝ))
  rw [add_div] at hb'
  have h := dist_bound G K hK
  change distance G - ((D.card:ℝ)/(n:ℝ)^2) ≤ _
  linarith

theorem solution {n : ℕ} (hn : 1 ≤ n) (G : Graph n) (ε lam : ℝ)
    (hε : 0 < ε ∧ ε < 1) (hlam : removalParameter ε ≤ ENNReal.ofReal lam) :
    scoreOpt G lam ≤ distance G ∧ distance G ≤ scoreOpt G lam + ε := by
  classical
  have h1 : ENNReal.ofReal 1 ≤ removalParameter ε := by
    apply le_sInf
    rintro _ ⟨R,hR,rfl⟩
    exact ENNReal.ofReal_le_ofReal hR.1
  have hl : (1 : ℝ) ≤ lam := ((ENNReal.ofReal_le_ofReal_iff').mp (h1.trans hlam)).resolve_right (by norm_num)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnonneg : 0 ≤ lam := by linarith
  constructor
  · apply le_csInf (dist_nonempty G)
    rintro x ⟨K,hK,rfl⟩
    let D := edges G \ edges K
    have hsub : D ⊆ edges G := Finset.sdiff_subset
    have Hle : edgeGraph (edges G \ D) ≤ K := by
      apply (SimpleGraph.fromEdgeSet_le K).mpr
      intro e he
      have h : e ∈ edges G \ D := he.1
      have hh : e ∈ edges K := by
        simp only [D, Finset.mem_sdiff] at h
        tauto
      exact SimpleGraph.mem_edgeFinset.mp hh
    have hz : triangles (edgeGraph (edges G \ D)) = 0 :=
      Finset.card_eq_zero.mpr (SimpleGraph.cliqueFinset_eq_empty_iff.mpr (hK.anti Hle))
    have hopt : scoreOpt G lam ≤ score G lam D := by
      unfold scoreOpt
      apply csInf_le _ (show _ ∈ {x : ℝ | ∃ F : EdgeSet n, F ⊆ edges G ∧ x = score G lam F} from ⟨D,hsub,rfl⟩)
      refine ⟨0, ?_⟩
      rintro x ⟨D,_,rfl⟩
      exact cost_nonneg G lam hnonneg D
    apply hopt.trans
    simp only [score,triangleDensity,hz,Nat.cast_zero,zero_div,mul_zero,add_zero,edgeDensity]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card (Finset.symmDiff_subset_sdiff (s:=edges G) (t:=edges K))) (sq_nonneg _)
  · rw [← sub_le_iff_le_add]
    apply le_csInf (show Set.Nonempty {r : ℝ | ∃ D : EdgeSet n, D ⊆ edges G ∧ r = score G lam D} from
      ⟨_,∅,Finset.empty_subset _,rfl⟩)
    rintro x ⟨D,hD,rfl⟩
    let H := edgeGraph (edges G \ D)
    have hres := residual_distance G D hD
    change distance G ≤ edgeDensity D + distance H at hres
    by_cases hd : distance H < ε
    · have hp : 0 ≤ lam * triangleDensity (edges G \ D) := by unfold triangleDensity; positivity
      unfold score
      linarith
    · have hpos : 0 < triangles H := by
        by_contra! hz
        have hf : triangleFree H := SimpleGraph.cliqueFinset_eq_empty_iff.mp
          (Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hz))
        have h := dist_bound H H hf
        simp at h
        linarith
      have ht : (0 : ℝ) < triangles H := by exact_mod_cast hpos
      have hlow : ENNReal.ofReal ((n:ℝ)^3 / triangles H) ≤ removalParameter ε := by
        apply le_sInf
        rintro _ ⟨R,hR,rfl⟩
        apply ENNReal.ofReal_le_ofReal
        obtain ⟨hr,hr'⟩ := hR
        have h := hr' n hn H (le_of_not_gt hd)
        apply (div_le_iff₀ ht).mpr
        have := (div_le_iff₀ (by linarith : (0:ℝ)<R)).mp h
        linarith
      have hratio := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp (hlow.trans hlam)
      have hprod := (div_le_iff₀ ht).mp hratio
      have hone : 1 ≤ lam * triangleDensity (edges G \ D) := by
        change 1 ≤ lam * ((triangles H : ℝ) / (n:ℝ)^3)
        rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
        linarith
      have hd0 : 0 ≤ edgeDensity D := by unfold edgeDensity; positivity
      unfold score
      linarith [dist_le_one hn G, hε.1]
#print axioms solution
