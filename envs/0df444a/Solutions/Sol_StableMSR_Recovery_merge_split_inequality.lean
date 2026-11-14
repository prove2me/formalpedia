-- Prove2me | solution 1 for StableMSR.Recovery.merge_split_inequality
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:07:00.772642+00:00
-- url     : https://prove2.me/submissions/47beed0c-5587-466f-8857-05e2cf6cb6b4

import Theorems.Thm_StableMSR_Recovery_split_perturbation

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery


set_option autoImplicit false
open scoped BigOperators

namespace MergeFinal

lemma sum_partition_three {α : Type*} [DecidableEq α]
    {O D F : Finset α} (hD : D ⊆ O) (hF : F ⊆ O) (hDF : Disjoint D F)
    (w : α → ℝ) :
    (∑ x ∈ O, w x) = (∑ x ∈ O \ (D ∪ F), w x) + (∑ x ∈ D, w x) +
      (∑ x ∈ F, w x) := by
  have hsub : D ∪ F ⊆ O := Finset.union_subset hD hF
  have hu : (O \ (D ∪ F)) ∪ (D ∪ F) = O := Finset.sdiff_union_of_subset hsub
  have hd : Disjoint (O \ (D ∪ F)) (D ∪ F) := Finset.sdiff_disjoint
  calc
    (∑ x ∈ O, w x) = ∑ x ∈ (O \ (D ∪ F)) ∪ (D ∪ F), w x :=
      congrArg (fun A : Finset α => ∑ x ∈ A, w x) hu.symm
    _ = (∑ x ∈ O \ (D ∪ F), w x) + ((∑ x ∈ D, w x) + (∑ x ∈ F, w x)) := by
      rw [Finset.sum_union hd, Finset.sum_union hDF]
    _ = _ := (add_assoc _ _ _).symm

end MergeFinal

namespace MergeAux

lemma radius_congr_on {n : ℕ} (d e : Point n → Point n → ℝ) (A : Cluster n)
    (heq : ∀ x ∈ A, ∀ y ∈ A, d x y = e x y) : radius d A = radius e A := by
  classical
  by_cases hA : A.Nonempty
  · simp only [radius, dif_pos hA]
    apply Finset.inf'_congr hA rfl
    intro x hx
    simp only [eccentricity, dif_pos hA]
    exact Finset.sup'_congr hA rfl (heq x hx)
  · simp only [radius, dif_neg hA]

lemma radius_singleton_of_diag {n : ℕ} (d : Point n → Point n → ℝ)
    (hdiag : ∀ x, d x x = 0) (x : Point n) : radius d {x} = 0 := by
  classical
  simp [radius, eccentricity, hdiag]

lemma perturbation_diag {n : ℕ} (d e : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (γ : ℝ) (he : Perturbation d γ e) :
    ∀ x, e x x = 0 := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  intro x
  have hx : d x x = 0 := by rw [← hm]; exact dist_self x
  have hb := he.2 x x
  rw [hx, mul_zero] at hb
  exact le_antisymm hb.2 hb.1

lemma glue_perturbations {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (γ : ℝ) (hγ : 1 < γ)
    (F : Partition n) (hFpair : (F : Set (Cluster n)).Pairwise Disjoint)
    (a : Cluster n → Point n → Point n → ℝ)
    (ha : ∀ C ∈ F, Perturbation d γ (a C)) :
    ∃ e : Point n → Point n → ℝ, Perturbation d γ e ∧
      (∀ C ∈ F, ∀ x ∈ C, ∀ y ∈ C, e x y = a C x y) ∧
      (∀ x y, (∀ C ∈ F, ¬ (x ∈ C ∧ y ∈ C)) → e x y = d x y) := by
  classical
  have huniq : ∀ A ∈ F, ∀ B ∈ F, ∀ x, x ∈ A → x ∈ B → A = B := by
    intro A hA B hB x hxA hxB
    by_contra hne
    exact Finset.disjoint_left.mp (hFpair hA hB hne) hxA hxB
  let S : Point n → Point n → Prop := fun x y => ∃ C ∈ F, x ∈ C ∧ y ∈ C
  let e : Point n → Point n → ℝ := fun x y =>
    if h : S x y then a h.choose x y else d x y
  have hins : ∀ C ∈ F, ∀ x ∈ C, ∀ y ∈ C, e x y = a C x y := by
    intro C hC x hx y hy
    have hs : S x y := ⟨C, hC, hx, hy⟩
    have hchoose : hs.choose = C :=
      huniq hs.choose hs.choose_spec.1 C hC x hs.choose_spec.2.1 hx
    simp only [e, dif_pos hs, hchoose]
  have hout : ∀ x y, (∀ C ∈ F, ¬ (x ∈ C ∧ y ∈ C)) → e x y = d x y := by
    intro x y hxy
    have hs : ¬ S x y := by
      rintro ⟨C, hC, hx, hy⟩
      exact hxy C hC ⟨hx, hy⟩
    simp only [e, dif_neg hs]
  obtain ⟨m, hm⟩ := hd
  letI := m
  have hdcomm : ∀ x y, d x y = d y x := by
    intro x y
    rw [← hm, ← hm]
    exact dist_comm x y
  have hdpos : ∀ x y, 0 ≤ d x y := by
    intro x y
    rw [← hm]
    exact dist_nonneg
  refine ⟨e, ⟨?_, ?_⟩, hins, hout⟩
  · intro x y
    by_cases hs : S x y
    · obtain ⟨C, hC, hx, hy⟩ := hs
      rw [hins C hC x hx y hy, hins C hC y hy x hx]
      exact (ha C hC).1 x y
    · have hs' : ¬ S y x := by
        rintro ⟨C, hC, hy, hx⟩
        exact hs ⟨C, hC, hx, hy⟩
      simp only [e, dif_neg hs, dif_neg hs', hdcomm]
  · intro x y
    by_cases hs : S x y
    · obtain ⟨C, hC, hx, hy⟩ := hs
      rw [hins C hC x hx y hy]
      exact (ha C hC).2 x y
    · simp only [e, dif_neg hs]
      exact ⟨le_rfl, by nlinarith [hdpos x y]⟩

end MergeAux


set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace MergeAux

private lemma nonempty_disjoint_ne {n : ℕ} {A B : Cluster n}
    (hA : A.Nonempty) (hAB : Disjoint A B) : A ≠ B := by
  intro h
  obtain ⟨x, hx⟩ := hA
  exact Finset.disjoint_left.mp hAB hx (h ▸ hx)

private lemma subblocks_disjoint {n : ℕ} {O : Partition n}
    (hO : (O : Set (Cluster n)).Pairwise Disjoint)
    {C D A B : Cluster n} (hC : C ∈ O) (hD : D ∈ O) (hne : C ≠ D)
    (hAC : A ⊆ C) (hBD : B ⊆ D) : Disjoint A B :=
  (hO hC hD hne).mono hAC hBD

private lemma erase_nonempty {n : ℕ} {C : Cluster n} (hC : 2 ≤ C.card)
    (p : Point n) : (C.erase p).Nonempty := by
  obtain ⟨x, hx, hxp⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) p
  exact ⟨x, Finset.mem_erase.mpr ⟨hxp, hx⟩⟩

private lemma split_properties {n : ℕ} {C : Cluster n} {p : Point n}
    (hC : 2 ≤ C.card) (hp : p ∈ C) :
    let S : Partition n := {C.erase p, {p}}
    S.card = 2 ∧ (∀ A ∈ S, A.Nonempty ∧ A ⊆ C) ∧
      (S : Set (Cluster n)).Pairwise Disjoint ∧ S.biUnion id = C := by
  classical
  have hne : C.erase p ≠ ({p} : Cluster n) := by
    intro h
    have hp' : p ∈ C.erase p := by rw [h]; simp
    simpa using hp'
  dsimp
  refine ⟨by simp [hne], ?_, ?_, ?_⟩
  · intro A hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl
    · exact ⟨erase_nonempty hC p, Finset.erase_subset p C⟩
    · exact ⟨Finset.singleton_nonempty p, by simpa using hp⟩
  · intro A hA B hB hAB
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (hAB rfl)
    · simp
    · simp
    · exact False.elim (hAB rfl)
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, id_eq, Finset.mem_erase]
    by_cases hxp : x = p
    · subst x; simp [hp]
    · simp [hxp]

lemma exchange_partition {n k : ℕ} (O D F : Partition n)
    (hO : Feasible Finset.univ k O) (hD : D ⊆ O) (hF : F ⊆ O)
    (hdisj : Disjoint D F) (hsize : 2 ≤ D.card) (hcount : F.card + 1 = D.card)
    (hns : ∀ C ∈ F, 2 ≤ C.card)
    (p : Cluster n → Point n) (hp : ∀ C ∈ F, p C ∈ C) :
    ∃ Q : Partition n, Feasible Finset.univ k Q ∧ Q ≠ O ∧
      ∀ w : Cluster n → ℝ, (∀ x, w {x} = 0) →
        (∑ C ∈ Q, w C) = (∑ C ∈ O \ (D ∪ F), w C) +
          w (D.biUnion id) + ∑ C ∈ F, w (C.erase (p C)) := by
  classical
  let R := O \ (D ∪ F)
  let M := D.biUnion id
  let pieces : Cluster n → Partition n := fun C => {C.erase (p C), {p C}}
  let S := F.biUnion pieces
  have hRsub : R ⊆ O := Finset.sdiff_subset
  have hsubDF : D ∪ F ⊆ O := Finset.union_subset hD hF
  have hOunion : (D ∪ F) ∪ R = O := Finset.union_sdiff_of_subset hsubDF
  have hpiece : ∀ C ∈ F, (pieces C).card = 2 ∧
      (∀ A ∈ pieces C, A.Nonempty ∧ A ⊆ C) ∧
      ((pieces C) : Set (Cluster n)).Pairwise Disjoint ∧ (pieces C).biUnion id = C := by
    intro C hC
    exact split_properties (hns C hC) (hp C hC)
  have hSpair : (F : Set (Cluster n)).PairwiseDisjoint pieces := by
    intro C hC E hE hCE
    apply Finset.disjoint_left.mpr
    intro A hAC hAE
    obtain ⟨x, hx⟩ := (hpiece C hC).2.1 A hAC |>.1
    exact Finset.disjoint_left.mp (hO.2.2.1 (hF hC) (hF hE) hCE)
      ((hpiece C hC).2.1 A hAC |>.2 hx) ((hpiece E hE).2.1 A hAE |>.2 hx)
  have hScard : S.card = 2 * F.card := by
    rw [Finset.card_biUnion hSpair]
    calc
      (∑ C ∈ F, (pieces C).card) = ∑ _C ∈ F, 2 := Finset.sum_congr rfl (fun C hC => (hpiece C hC).1)
      _ = 2 * F.card := by simp [mul_comm]
  have hSmem : ∀ A ∈ S, ∃ C ∈ F, A ∈ pieces C := by
    intro A hA
    exact Finset.mem_biUnion.mp hA
  have hSnonempty : ∀ A ∈ S, A.Nonempty := by
    intro A hA
    obtain ⟨C, hC, hAC⟩ := hSmem A hA
    exact ((hpiece C hC).2.1 A hAC).1
  have hSpw : (S : Set (Cluster n)).Pairwise Disjoint := by
    intro A hA B hB hAB
    obtain ⟨C, hC, hAC⟩ := hSmem A hA
    obtain ⟨E, hE, hBE⟩ := hSmem B hB
    by_cases hCE : C = E
    · subst E
      exact (hpiece C hC).2.2.1 hAC hBE hAB
    · exact subblocks_disjoint hO.2.2.1 (hF hC) (hF hE) hCE
        ((hpiece C hC).2.1 A hAC).2 ((hpiece E hE).2.1 B hBE).2
  have hRSblocks : ∀ A ∈ R, ∀ B ∈ S, Disjoint A B := by
    intro A hA B hB
    obtain ⟨C, hC, hBC⟩ := hSmem B hB
    have hAC : A ≠ C := by
      intro heq
      apply (Finset.mem_sdiff.mp hA).2
      rw [heq]
      exact Finset.mem_union_right D hC
    exact (hO.2.2.1 (hRsub hA) (hF hC) hAC).mono_right ((hpiece C hC).2.1 B hBC).2
  have hRSdisj : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro A hAR hAS
    exact nonempty_disjoint_ne (hSnonempty A hAS) (hRSblocks A hAR A hAS) rfl
  have hMne : M.Nonempty := by
    obtain ⟨C, hC⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
    obtain ⟨x, hx⟩ := hO.2.1 C (hD hC)
    exact ⟨x, Finset.mem_biUnion.mpr ⟨C, hC, hx⟩⟩
  have hMout : ∀ C ∈ O, C ∉ D → Disjoint M C := by
    intro C hC hnD
    apply Finset.disjoint_left.mpr
    intro x hxM hxC
    obtain ⟨E, hE, hxE⟩ := Finset.mem_biUnion.mp hxM
    have hEC : E ≠ C := by intro heq; exact hnD (heq ▸ hE)
    exact Finset.disjoint_left.mp (hO.2.2.1 (hD hE) hC hEC) hxE hxC
  have hMR : ∀ A ∈ R, Disjoint M A := by
    intro A hA
    apply hMout A (hRsub hA)
    intro hAD
    exact (Finset.mem_sdiff.mp hA).2 (Finset.mem_union_left F hAD)
  have hMS : ∀ A ∈ S, Disjoint M A := by
    intro A hA
    obtain ⟨C, hC, hAC⟩ := hSmem A hA
    have hCnD : C ∉ D := fun hCD => Finset.disjoint_left.mp hdisj hCD hC
    exact (hMout C (hF hC) hCnD).mono_right ((hpiece C hC).2.1 A hAC).2
  have hMnRS : M ∉ R ∪ S := by
    intro h
    rcases Finset.mem_union.mp h with hR | hS
    · exact nonempty_disjoint_ne hMne (hMR M hR) rfl
    · exact nonempty_disjoint_ne hMne (hMS M hS) rfl
  let Q := insert M (R ∪ S)
  have hQfeas : Feasible Finset.univ k Q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (insert M (R ∪ S)).card = k
      rw [Finset.card_insert_of_notMem hMnRS, Finset.card_union_of_disjoint hRSdisj, hScard]
      have hCard : (D ∪ F).card + R.card = O.card := by
        rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right, hOunion]
      rw [Finset.card_union_of_disjoint hdisj, hO.1] at hCard
      omega
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hMne
      rcases Finset.mem_union.mp hA with hA | hA
      · exact hO.2.1 A (hRsub hA)
      · exact hSnonempty A hA
    · intro A hA B hB hAB
      rcases Finset.mem_insert.mp hA with rfl | hA
      · rcases Finset.mem_insert.mp hB with rfl | hB
        · exact False.elim (hAB rfl)
        rcases Finset.mem_union.mp hB with hB | hB
        · exact hMR B hB
        · exact hMS B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · rcases Finset.mem_union.mp hA with hA | hA
        · exact (hMR A hA).symm
        · exact (hMS A hA).symm
      rcases Finset.mem_union.mp hA with hAR | hAS <;>
        rcases Finset.mem_union.mp hB with hBR | hBS
      · exact hO.2.2.1 (hRsub hAR) (hRsub hBR) hAB
      · exact hRSblocks A hAR B hBS
      · exact (hRSblocks B hBR A hAS).symm
      · exact hSpw hAS hBS hAB
    · have hScover : S.biUnion id = F.biUnion id := by
        change (F.biUnion pieces).biUnion id = F.biUnion id
        rw [Finset.biUnion_biUnion]
        apply Finset.biUnion_congr rfl
        intro C hC
        exact (hpiece C hC).2.2.2
      change (insert M (R ∪ S)).biUnion id = Finset.univ
      rw [Finset.biUnion_insert, Finset.union_biUnion, hScover]
      rw [show M = D.biUnion id from rfl]
      simp only [id_eq]
      rw [← Finset.union_biUnion, ← Finset.union_biUnion]
      have heq : D ∪ (R ∪ F) = O := by
        rw [Finset.union_comm R F, ← Finset.union_assoc, hOunion]
      rw [heq]
      exact hO.2.2.2
  have hQne : Q ≠ O := by
    intro heq
    have hMO : M ∈ O := by rw [← heq]; exact Finset.mem_insert_self M _
    obtain ⟨C, hCD, hCM⟩ := Finset.exists_mem_ne (by omega : 1 < D.card) M
    obtain ⟨x, hxC⟩ := hO.2.1 C (hD hCD)
    have hxM : x ∈ M := Finset.mem_biUnion.mpr ⟨C, hCD, hxC⟩
    exact Finset.disjoint_left.mp (hO.2.2.1 (hD hCD) hMO hCM) hxC hxM
  refine ⟨Q, hQfeas, hQne, ?_⟩
  intro w hw
  change (∑ C ∈ insert M (R ∪ S), w C) = (∑ C ∈ R, w C) + w M + ∑ C ∈ F, w (C.erase (p C))
  rw [Finset.sum_insert hMnRS, Finset.sum_union hRSdisj]
  have hSsum : (∑ C ∈ S, w C) = ∑ C ∈ F, w (C.erase (p C)) := by
    change (∑ C ∈ F.biUnion pieces, w C) = _
    rw [Finset.sum_biUnion hSpair]
    apply Finset.sum_congr rfl
    intro C hC
    have hne : C.erase (p C) ≠ ({p C} : Cluster n) := by
      intro heq
      have hx : p C ∈ C.erase (p C) := by rw [heq]; simp
      simpa using hx
    simp [pieces, hne, hw]
  rw [hSsum]
  ring

end MergeAux

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (D F : Partition n) (hD : D ⊆ O) (hF : F ⊆ O)
    (hdisj : Disjoint D F) (hsize : 2 ≤ D.card) (hcount : F.card + 1 = D.card)
    (hnonsingleton : ∀ C ∈ F, 2 ≤ C.card) :
    cost d D + (γ - 1) * cost d F < radius d (D.biUnion id) := by
  classical
  let z : Point n := ⟨0, by omega⟩
  have hdata : ∀ C : Cluster n, ∃ p : Point n, ∃ a : Point n → Point n → ℝ,
      C ∈ F → p ∈ C ∧ Perturbation d γ a ∧
        radius a C = γ * radius d C ∧ radius a (C.erase p) ≤ radius d C := by
    intro C
    by_cases hCF : C ∈ F
    · obtain ⟨c, p, hc, hp, hpc, a, ha, hout, hr, hrem⟩ :=
        split_perturbation d hd γ hγ C (hnonsingleton C hCF)
      exact ⟨p, a, fun _ => ⟨hp, ha, hr, hrem⟩⟩
    · exact ⟨z, d, by intro h; exact False.elim (hCF h)⟩
  choose p a hpa using hdata
  have hFpair : (F : Set (Cluster n)).Pairwise Disjoint := by
    intro A hA B hB hne
    exact hO.1.2.2.1 (hF hA) (hF hB) hne
  obtain ⟨e, he, hins, hout⟩ :=
    MergeAux.glue_perturbations d hd γ hγ F hFpair a (fun C hC => (hpa C hC).2.1)
  have hrF : ∀ C ∈ F, radius e C = γ * radius d C := by
    intro C hC
    rw [MergeAux.radius_congr_on e (a C) C (hins C hC)]
    exact (hpa C hC).2.2.1
  have hrrem : ∀ C ∈ F, radius e (C.erase (p C)) ≤ radius d C := by
    intro C hC
    rw [MergeAux.radius_congr_on e (a C) (C.erase (p C)) (by
      intro x hx y hy
      exact hins C hC x (Finset.mem_erase.mp hx).2 y (Finset.mem_erase.mp hy).2)]
    exact (hpa C hC).2.2.2
  have hroutside : ∀ C ∈ O, C ∉ F → radius e C = radius d C := by
    intro C hCO hCF
    apply MergeAux.radius_congr_on
    intro x hx y hy
    apply hout
    intro A hA hxy
    have hCA : C ≠ A := by
      intro h
      subst A
      exact hCF hA
    exact Finset.disjoint_left.mp (hO.1.2.2.1 hCO (hF hA) hCA) hx hxy.1
  have hrmerged : radius e (D.biUnion id) = radius d (D.biUnion id) := by
    apply MergeAux.radius_congr_on
    intro x hx y hy
    obtain ⟨C, hCD, hxC⟩ := Finset.mem_biUnion.mp hx
    apply hout
    intro A hA hxy
    have hCA : C ≠ A := by
      intro h
      subst A
      exact Finset.disjoint_left.mp hdisj hCD hA
    exact Finset.disjoint_left.mp (hO.1.2.2.1 (hD hCD) (hF hA) hCA) hxC hxy.1
  let T := O \ (D ∪ F)
  have hcostT : cost e T = cost d T := by
    unfold cost
    apply Finset.sum_congr rfl
    intro C hC
    obtain ⟨hCO, hCDF⟩ := Finset.mem_sdiff.mp hC
    exact hroutside C hCO (fun hCF => hCDF (Finset.mem_union_right D hCF))
  have hcostD : cost e D = cost d D := by
    unfold cost
    apply Finset.sum_congr rfl
    intro C hC
    exact hroutside C (hD hC) (fun hCF => Finset.disjoint_left.mp hdisj hC hCF)
  have hcostF : cost e F = γ * cost d F := by
    unfold cost
    calc
      (∑ C ∈ F, radius e C) = ∑ C ∈ F, γ * radius d C := Finset.sum_congr rfl hrF
      _ = _ := by
        have hmul : ∀ G : Partition n, (∑ C ∈ G, γ * radius d C) =
            γ * (∑ C ∈ G, radius d C) := by
          intro G
          induction G using Finset.induction_on with
          | empty => simp
          | @insert C G hCG ih => simp [hCG, ih, mul_add]
        exact hmul F
  have hcostO : cost e O = cost d T + cost d D + γ * cost d F := by
    have h := MergeFinal.sum_partition_three hD hF hdisj (radius e)
    change cost e O = cost e T + cost e D + cost e F at h
    simpa only [hcostT, hcostD, hcostF] using h
  obtain ⟨Q, hQ, hQne, hQcost⟩ :=
    MergeAux.exchange_partition O D F hO.1 hD hF hdisj hsize hcount hnonsingleton p
      (fun C hC => (hpa C hC).1)
  have hsumrem : (∑ C ∈ F, radius e (C.erase (p C))) ≤ cost d F :=
    Finset.sum_le_sum hrrem
  have hcostQ : cost e Q ≤ cost d T + radius d (D.biUnion id) + cost d F := by
    have h := hQcost (radius e)
      (MergeAux.radius_singleton_of_diag e (MergeAux.perturbation_diag d e hd γ he))
    change cost e Q = cost e T + radius e (D.biUnion id) +
      (∑ C ∈ F, radius e (C.erase (p C))) at h
    rw [hcostT, hrmerged] at h
    linarith
  have hu := hO.2 e he
  have hle : cost e O ≤ cost e Q := hu.1.2 Q hQ
  have hneq : cost e O ≠ cost e Q := by
    intro heq
    have hQopt : Optimal e Finset.univ k Q := by
      refine ⟨hQ, ?_⟩
      intro R hR
      rw [← heq]
      exact hu.1.2 R hR
    exact hQne (hu.2 Q hQopt)
  have hstrict : cost e O < cost e Q := lt_of_le_of_ne hle hneq
  rw [hcostO] at hstrict
  nlinarith
