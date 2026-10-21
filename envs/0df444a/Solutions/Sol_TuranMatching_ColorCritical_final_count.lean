-- Prove2me | solution 1 for TuranMatching.ColorCritical.final_count
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:52:51.793874+00:00
-- url     : https://prove2.me/submissions/ffabfbc1-f1ab-4a32-b376-fc01d949065c

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

set_option autoImplicit false
open Finset SimpleGraph

namespace TMCAux

lemma adj_lt_ge (n k s : ℕ) (hk : 2 ≤ k) (v w : Fin n) (hv : (v : ℕ) < s) (hw : s ≤ (w : ℕ)) :
    (TuranMatching.Clique.bigGraph n k s).Adj v w := by
  show TuranMatching.Clique.bigClass k s v ≠ TuranMatching.Clique.bigClass k s w
  simp only [TuranMatching.Clique.bigClass, hv, if_true, not_lt.mpr hw, if_false]
  have : (v : ℕ) % (k - 1) < k - 1 := Nat.mod_lt _ (by omega)
  omega

lemma cross_exists (n k s : ℕ) (hk : 2 ≤ k) (hsn : s ≤ n) :
    ∃ C : Finset (Sym2 (Fin n)), C ⊆ (TuranMatching.Clique.bigGraph n k s).edgeFinset ∧
      s * (n - s) ≤ C.card ∧ ∀ e ∈ C, ∃ v ∈ e, s ≤ (v : ℕ) := by
  classical
  rcases hsn.lt_or_eq with hsn | rfl
  · let a : Fin n := ⟨s, hsn⟩
    let A : Finset (Fin n) := Finset.Iio a
    let B : Finset (Fin n) := Finset.Ici a
    have hA : #A = s := by simp [A, a]
    have hB : #B = n - s := by simp [B, a]
    have hcls : ∀ v w : Fin n, v ∈ A → w ∈ B → (TuranMatching.Clique.bigGraph n k s).Adj v w := by
      intro v w hv hw
      exact adj_lt_ge n k s hk v w (Fin.lt_def.mp (Finset.mem_Iio.mp hv))
        (Fin.le_def.mp (Finset.mem_Ici.mp hw))
    have hsub : ((A ×ˢ B).image (fun p : Fin n × Fin n => s(p.1, p.2))) ⊆
        (TuranMatching.Clique.bigGraph n k s).edgeFinset := by
      intro e he
      obtain ⟨⟨v, w⟩, hp, rfl⟩ := Finset.mem_image.mp he
      rw [Finset.mem_product] at hp
      simpa using hcls v w hp.1 hp.2
    have hinj : Set.InjOn (fun p : Fin n × Fin n => s(p.1, p.2)) (A ×ˢ B : Finset _) := by
      intro p hp q hq h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
      have hp1 : (p.1 : ℕ) < s := Fin.lt_def.mp (Finset.mem_Iio.mp hp.1)
      have hp2 : s ≤ (p.2 : ℕ) := Fin.le_def.mp (Finset.mem_Ici.mp hp.2)
      have hq1 : (q.1 : ℕ) < s := Fin.lt_def.mp (Finset.mem_Iio.mp hq.1)
      have hq2 : s ≤ (q.2 : ℕ) := Fin.le_def.mp (Finset.mem_Ici.mp hq.2)
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso; have := congrArg Fin.val h1; omega
    refine ⟨(A ×ˢ B).image (fun p : Fin n × Fin n => s(p.1, p.2)), hsub, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hinj, Finset.card_product, hA, hB]
    · intro e he
      obtain ⟨⟨v, w⟩, hp, rfl⟩ := Finset.mem_image.mp he
      rw [Finset.mem_product] at hp
      exact ⟨w, Sym2.mem_mk_right _ _, Fin.le_def.mp (Finset.mem_Ici.mp hp.2)⟩
  · exact ⟨∅, by simp, by simp, by simp⟩

lemma gNum_ge2 (n k s : ℕ) (hk : 2 ≤ k) (hsn : s ≤ n) :
    TuranMatching.Clique.turanNum s (k - 1) + s * (n - s) ≤ TuranMatching.Clique.gNum n k s := by
  classical
  obtain ⟨C, hCsub, hCcard, hCv⟩ := cross_exists n k s hk hsn
  let φ : Fin s → Fin n := Fin.castLE hsn
  have hφ : Function.Injective φ := Fin.castLE_injective hsn
  let I : Finset (Sym2 (Fin n)) := (turanGraph s (k - 1)).edgeFinset.image (Sym2.map φ)
  have hIcard : I.card = TuranMatching.Clique.turanNum s (k - 1) := by
    unfold TuranMatching.Clique.turanNum
    exact Finset.card_image_of_injective _ (Sym2.map.injective hφ)
  have hIsub : I ⊆ (TuranMatching.Clique.bigGraph n k s).edgeFinset := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
    induction e0 using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, turanGraph_adj] at he0
      simp only [Sym2.map_pair_eq, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      show TuranMatching.Clique.bigClass k s (φ a) ≠ TuranMatching.Clique.bigClass k s (φ b)
      have ha : (φ a : ℕ) < s := a.2
      have hb : (φ b : ℕ) < s := b.2
      simp only [TuranMatching.Clique.bigClass, ha, hb, if_true]
      simpa [φ] using he0
  have hdisj : Disjoint I C := by
    rw [Finset.disjoint_left]
    intro e heI heC
    obtain ⟨v, hv, hvs⟩ := hCv e heC
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp heI
    induction e0 using Sym2.ind with
    | h a b =>
      rw [Sym2.map_pair_eq, Sym2.mem_iff] at hv
      have ha : (φ a : ℕ) < s := a.2
      have hb : (φ b : ℕ) < s := b.2
      rcases hv with rfl | rfl <;> omega
  calc TuranMatching.Clique.turanNum s (k - 1) + s * (n - s) ≤ I.card + C.card := by omega
    _ = (I ∪ C).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ _ := Finset.card_le_card (Finset.union_subset hIsub hCsub)

lemma turanNum_shift (k s : ℕ) (hk : 2 ≤ k) :
    TuranMatching.Clique.turanNum (s + s / (k - 1)) k =
      TuranMatching.Clique.turanNum s (k - 1) + (s / (k - 1)) * s := by
  obtain ⟨u, rfl⟩ : ∃ u, k = u + 2 := ⟨k - 2, by omega⟩
  have e1 : u + 2 - 1 = u + 1 := by omega
  rw [e1]
  unfold TuranMatching.Clique.turanNum
  rw [SimpleGraph.card_edgeFinset_turanGraph, SimpleGraph.card_edgeFinset_turanGraph]
  set q := s / (u + 1) with hq
  set ρ := s % (u + 1) with hρ
  have hρlt : ρ < u + 1 := Nat.mod_lt _ (by omega)
  have hs : s = (u + 1) * q + ρ := (Nat.div_add_mod s (u + 1)).symm
  have hN : (s + q) % (u + 2) = ρ := by
    rw [show s + q = ρ + (u + 2) * q by rw [hs]; ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hN]
  have h1 : ((s + q) ^ 2 - ρ ^ 2) * (u + 2 - 1) / (2 * (u + 2)) =
      q * ((u + 2) * q + 2 * ρ) * (u + 1) / 2 := by
    have : (s + q) ^ 2 - ρ ^ 2 = (u + 2) * (q * ((u + 2) * q + 2 * ρ)) := by
      have hh : (s + q) ^ 2 = ρ ^ 2 + (u + 2) * (q * ((u + 2) * q + 2 * ρ)) := by
        rw [hs]; ring
      omega
    rw [this, show u + 2 - 1 = u + 1 by omega,
      show (u + 2) * (q * ((u + 2) * q + 2 * ρ)) * (u + 1) =
        (u + 2) * (q * ((u + 2) * q + 2 * ρ) * (u + 1)) by ring,
      show 2 * (u + 2) = (u + 2) * 2 by ring]
    exact Nat.mul_div_mul_left _ _ (by omega)
  have h2 : (s ^ 2 - ρ ^ 2) * (u + 1 - 1) / (2 * (u + 1)) =
      q * ((u + 1) * q + 2 * ρ) * u / 2 := by
    have : s ^ 2 - ρ ^ 2 = (u + 1) * (q * ((u + 1) * q + 2 * ρ)) := by
      have hh : s ^ 2 = ρ ^ 2 + (u + 1) * (q * ((u + 1) * q + 2 * ρ)) := by
        rw [hs]; ring
      omega
    rw [this, show u + 1 - 1 = u by omega,
      show (u + 1) * (q * ((u + 1) * q + 2 * ρ)) * u =
        (u + 1) * (q * ((u + 1) * q + 2 * ρ) * u) by ring,
      show 2 * (u + 1) = (u + 1) * 2 by ring]
    exact Nat.mul_div_mul_left _ _ (by omega)
  rw [h1, h2]
  have h3 : q * ((u + 2) * q + 2 * ρ) * (u + 1) =
      q * ((u + 1) * q + 2 * ρ) * u + 2 * (q * s) := by
    rw [hs]; ring
  rw [h3, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
  ring

end TMCAux

theorem solution {n k s : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Z : Finset (Fin n)) (hX : #X = s) (hXZ : Disjoint X Z) (hZ : #Z = s / (k - 1))
    (hind : ∀ y z : Fin n, y ∉ X → z ∉ X → ¬ G.Adj y z)
    (hT : #(G.edgeFinset ∩ (X ∪ Z).sym2) ≤ TuranMatching.Clique.turanNum (s + s / (k - 1)) k) :
    #G.edgeFinset ≤ TuranMatching.Clique.gNum n k s := by
  classical
  have hS : #(X ∪ Z) = s + s / (k - 1) := by
    rw [Finset.card_union_of_disjoint hXZ, hX, hZ]
  have hSn : #(X ∪ Z) ≤ n := by
    simpa using Finset.card_le_univ (X ∪ Z)
  have hsub : G.edgeFinset ⊆ (G.edgeFinset ∩ (X ∪ Z).sym2) ∪
      ((X ×ˢ (X ∪ Z)ᶜ).image (fun p : Fin n × Fin n => s(p.1, p.2))) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      by_cases hab : a ∈ X ∪ Z ∧ b ∈ X ∪ Z
      · apply Finset.mem_union_left
        rw [Finset.mem_inter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mk_mem_sym2_iff]
        exact ⟨he, hab⟩
      · apply Finset.mem_union_right
        rw [Finset.mem_image]
        rw [not_and_or] at hab
        rcases hab with ha | hb
        · have haX : a ∉ X := fun h => ha (Finset.mem_union_left _ h)
          have hbX : b ∈ X := by
            by_contra hbX
            exact hind a b haX hbX he
          refine ⟨(b, a), ?_, Sym2.eq_swap⟩
          rw [Finset.mem_product]
          exact ⟨hbX, by simpa using ha⟩
        · have hbX : b ∉ X := fun h => hb (Finset.mem_union_left _ h)
          have haX : a ∈ X := by
            by_contra haX
            exact hind a b haX hbX he
          refine ⟨(a, b), ?_, rfl⟩
          rw [Finset.mem_product]
          exact ⟨haX, by simpa using hb⟩
  have hc2 : #((X ×ˢ (X ∪ Z)ᶜ).image (fun p : Fin n × Fin n => s(p.1, p.2))) ≤ s * (n - (s + s / (k - 1))) := by
    calc _ ≤ #(X ×ˢ (X ∪ Z)ᶜ) := Finset.card_image_le
      _ = s * (n - (s + s / (k - 1))) := by
        rw [Finset.card_product, Finset.card_compl, hS, hX]
        simp
  have hsn : s ≤ n := by
    have := Finset.card_le_univ X
    simpa [hX] using this
  have hg := TMCAux.gNum_ge2 n k s hk hsn
  have hts := TMCAux.turanNum_shift k s hk
  have h1 : #G.edgeFinset ≤ #(G.edgeFinset ∩ (X ∪ Z).sym2) + s * (n - (s + s / (k - 1))) :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hc2 _))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hS ▸ hSn : s + s / (k - 1) ≤ n)
  have e1 : n - (s + s / (k - 1)) = d := by omega
  have e2 : n - s = s / (k - 1) + d := by omega
  rw [e1] at h1
  rw [e2] at hg
  have : s * (s / (k - 1) + d) = s / (k - 1) * s + s * d := by ring
  omega
