-- Prove2me | solution 1 for StableMSR.Recovery.contained_cluster_radii
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:18:24.792048+00:00
-- url     : https://prove2.me/submissions/3c0c5344-2e6a-4b33-9c42-7b3c88bfdf23

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace RefineAux

private lemma refine_exists_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  classical
  obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  exact ⟨c, hc, by simpa [radius, hC] using he.symm⟩

private lemma refine_dist_bound {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c x : Point n} (hc : OptimalCenter d C c) (hx : x ∈ C) :
    d c x ≤ radius d C := by
  rw [← hc.2, eccentricity, dif_pos ⟨c, hc.1⟩]
  exact Finset.le_sup' _ hx

private lemma refine_radius_bound {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {c : Point n} (hc : c ∈ C) {r : ℝ}
    (hb : ∀ x ∈ C, d c x ≤ r) : radius d C ≤ r := by
  rw [radius, dif_pos ⟨c, hc⟩]
  apply (Finset.inf'_le _ hc).trans
  rw [eccentricity, dif_pos ⟨c, hc⟩]
  exact Finset.sup'_le _ _ hb

private lemma refine_singleton_zero {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (p : Point n) : radius d {p} = 0 := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  have hself : d p p = 0 := by rw [← hm]; exact dist_self p
  simp [radius, eccentricity, hself]

lemma feasible_nonsingleton {n j : ℕ} (Q : Partition n)
    (hQ : Feasible Finset.univ j Q) (hjn : j < n) :
    ∃ C ∈ Q, 2 ≤ C.card := by
  classical
  by_contra hn
  have hcard : ∀ C ∈ Q, C.card = 1 := by
    intro C hC
    have hlo : 0 < C.card := Finset.card_pos.mpr (hQ.2.1 C hC)
    have hhi : ¬ 2 ≤ C.card := fun hh => hn ⟨C, hC, hh⟩
    omega
  have hsum : (Q.biUnion id).card = ∑ C ∈ Q, C.card :=
    Finset.card_biUnion hQ.2.2.1
  rw [hQ.2.2.2] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have heq : (∑ C ∈ Q, C.card) = Q.card := by
    calc
      (∑ C ∈ Q, C.card) = ∑ _C ∈ Q, 1 := Finset.sum_congr rfl hcard
      _ = Q.card := by simp
  rw [heq, hQ.1] at hsum
  omega

lemma split_one_partition {n j : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (Q : Partition n)
    (hQ : Feasible Finset.univ j Q) (hjn : j < n) :
    ∃ R : Partition n, Feasible Finset.univ (j + 1) R ∧ cost d R ≤ cost d Q := by
  classical
  obtain ⟨C, hCQ, hCsize⟩ := feasible_nonsingleton Q hQ hjn
  obtain ⟨c, hc⟩ := refine_exists_center d (hQ.2.1 C hCQ)
  obtain ⟨p, hpC, hpc⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) c
  let A := C.erase p
  let B : Cluster n := {p}
  let T := Q.erase C
  have hAne : A.Nonempty := ⟨c, Finset.mem_erase.mpr ⟨Ne.symm hpc, hc.1⟩⟩
  have hBne : B.Nonempty := Finset.singleton_nonempty p
  have hAC : A ⊆ C := Finset.erase_subset p C
  have hBC : B ⊆ C := by simpa [B] using hpC
  have hAB : Disjoint A B := by simp [A, B]
  have hABne : A ≠ B := by
    intro heq
    obtain ⟨x, hx⟩ := hAne
    exact Finset.disjoint_left.mp hAB hx (heq ▸ hx)
  have hTsub : T ⊆ Q := Finset.erase_subset C Q
  have hCD : ∀ D ∈ T, Disjoint C D := by
    intro D hD
    obtain ⟨hDC, hDQ⟩ := Finset.mem_erase.mp hD
    exact hQ.2.2.1 hCQ hDQ (Ne.symm hDC)
  have hAnT : A ∉ T := by
    intro hA
    obtain ⟨x, hx⟩ := hAne
    exact Finset.disjoint_left.mp (hCD A hA) (hAC hx) hx
  have hBnT : B ∉ T := by
    intro hB
    exact Finset.disjoint_left.mp (hCD B hB) hpC (Finset.mem_singleton_self p)
  have hAnBT : A ∉ insert B T := by simp [hABne, hAnT]
  let R := insert A (insert B T)
  have hfeas : Feasible Finset.univ (j + 1) R := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (insert A (insert B T)).card = j + 1
      rw [Finset.card_insert_of_notMem hAnBT, Finset.card_insert_of_notMem hBnT]
      have hTcard : T.card + 1 = Q.card := Finset.card_erase_add_one hCQ
      rw [hQ.1] at hTcard
      omega
    · intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hAne
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hBne
      exact hQ.2.1 D (hTsub hD)
    · intro D hD E hE hDE
      rcases Finset.mem_insert.mp hD with rfl | hD
      · rcases Finset.mem_insert.mp hE with rfl | hE
        · exact False.elim (hDE rfl)
        rcases Finset.mem_insert.mp hE with rfl | hE
        · exact hAB
        · exact (hCD E hE).mono_left hAC
      rcases Finset.mem_insert.mp hE with rfl | hE
      · rcases Finset.mem_insert.mp hD with rfl | hD
        · exact hAB.symm
        · exact ((hCD D hD).mono_left hAC).symm
      rcases Finset.mem_insert.mp hD with rfl | hD
      · rcases Finset.mem_insert.mp hE with rfl | hE
        · exact False.elim (hDE rfl)
        · exact (hCD E hE).mono_left hBC
      rcases Finset.mem_insert.mp hE with rfl | hE
      · exact ((hCD D hD).mono_left hBC).symm
      · exact hQ.2.2.1 (hTsub hD) (hTsub hE) hDE
    · have hab : A ∪ B = C := by
        ext x
        by_cases hxp : x = p
        · subst x; simp [A, B, hpC]
        · simp [A, B, hxp]
      have hCT : insert C T = Q := Finset.insert_erase hCQ
      change (insert A (insert B T)).biUnion id = Finset.univ
      rw [Finset.biUnion_insert, Finset.biUnion_insert]
      simp only [id_eq]
      rw [← Finset.union_assoc, hab]
      have hcov : (insert C T).biUnion id = Finset.univ := by
        rw [hCT]
        exact hQ.2.2.2
      simpa only [Finset.biUnion_insert, id_eq] using hcov
  refine ⟨R, hfeas, ?_⟩
  have hradA : radius d A ≤ radius d C := by
    apply refine_radius_bound d (Finset.mem_erase.mpr ⟨Ne.symm hpc, hc.1⟩)
    intro x hx
    exact refine_dist_bound hc (hAC hx)
  have hradB : radius d B = 0 := refine_singleton_zero d hd p
  have hcostQ : cost d Q = radius d C + cost d T := by
    have heq : Q = insert C T := (Finset.insert_erase hCQ).symm
    calc
      cost d Q = cost d (insert C T) := congrArg (cost d) heq
      _ = radius d C + cost d T := by
        unfold cost
        rw [Finset.sum_insert (by simp [T])]
  have hcostR : cost d R = radius d A + radius d B + cost d T := by
    change (∑ D ∈ insert A (insert B T), radius d D) = _
    rw [Finset.sum_insert hAnBT, Finset.sum_insert hBnT]
    simp only [cost]
    exact (add_assoc _ _ _).symm
  rw [hcostQ, hcostR, hradB]
  linarith

lemma refine_partition {n j k : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (Q : Partition n)
    (hQ : Feasible Finset.univ j Q) (hjk : j ≤ k) (hkn : k ≤ n) :
    ∃ R : Partition n, Feasible Finset.univ k R ∧ cost d R ≤ cost d Q := by
  revert hkn
  induction k, hjk using Nat.le_induction with
  | base =>
      intro _
      exact ⟨Q, hQ, le_rfl⟩
  | succ k hjk ih =>
      intro hkn
      obtain ⟨R, hR, hcostR⟩ := ih (by omega)
      obtain ⟨S, hS, hcostS⟩ := split_one_partition d hd R hR (by omega)
      exact ⟨S, hS, hcostS.trans hcostR⟩

end RefineAux

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace ContainedAux

lemma block_subset {n j : ℕ} {U : Cluster n} {Q : Partition n}
    (hQ : Feasible U j Q) {C : Cluster n} (hC : C ∈ Q) : C ⊆ U := by
  intro x hx
  rw [← hQ.2.2.2]
  exact Finset.mem_biUnion.mpr ⟨C, hC, hx⟩

lemma outside_union_disjoint {n k : ℕ} {O A : Partition n}
    (hO : Feasible Finset.univ k O) (hA : A ⊆ O)
    {C : Cluster n} (hC : C ∈ O \ A) : Disjoint C (A.biUnion id) := by
  classical
  obtain ⟨hCO, hCA⟩ := Finset.mem_sdiff.mp hC
  apply Finset.disjoint_left.mpr
  intro x hx hxA
  obtain ⟨B, hBA, hxB⟩ := Finset.mem_biUnion.mp hxA
  have hCB : C ≠ B := by
    intro h
    exact hCA (by simpa [h] using hBA)
  exact Finset.disjoint_left.mp (hO.2.2.1 hCO (hA hBA) hCB) hx hxB

lemma splice_disjoint {n k j : ℕ} {O A Q : Partition n}
    (hO : Feasible Finset.univ k O) (hA : A ⊆ O)
    (hQ : Feasible (A.biUnion id) j Q) : Disjoint Q (O \ A) := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hCQ hCT
  obtain ⟨x, hx⟩ := hQ.2.1 C hCQ
  exact Finset.disjoint_left.mp (outside_union_disjoint hO hA hCT)
    hx (block_subset hQ hCQ hx)

lemma splice_feasible {n k j : ℕ} {O A Q : Partition n}
    (hO : Feasible Finset.univ k O) (hA : A ⊆ O)
    (hQ : Feasible (A.biUnion id) j Q) :
    Feasible Finset.univ (j + (O \ A).card) (Q ∪ (O \ A)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint (splice_disjoint hO hA hQ), hQ.1]
  · intro C hC
    rcases Finset.mem_union.mp hC with hCQ | hCT
    · exact hQ.2.1 C hCQ
    · exact hO.2.1 C (Finset.mem_sdiff.mp hCT).1
  · intro C hC B hB hCB
    rcases Finset.mem_union.mp hC with hCQ | hCT <;>
      rcases Finset.mem_union.mp hB with hBQ | hBT
    · exact hQ.2.2.1 hCQ hBQ hCB
    · exact ((outside_union_disjoint hO hA hBT).mono_right (block_subset hQ hCQ)).symm
    · exact (outside_union_disjoint hO hA hCT).mono_right (block_subset hQ hBQ)
    · exact hO.2.2.1 (Finset.mem_sdiff.mp hCT).1 (Finset.mem_sdiff.mp hBT).1 hCB
  · rw [Finset.union_biUnion, hQ.2.2.2, ← Finset.union_biUnion,
      Finset.union_sdiff_of_subset hA]
    exact hO.2.2.2

lemma replacement_bound {n k j : ℕ} (d : Point n → Point n → ℝ)
    {O A Q : Partition n} (hO : Optimal d Finset.univ k O) (hA : A ⊆ O)
    (hQ : Feasible (A.biUnion id) j Q) (hj : j ≤ A.card)
    (hrefine : ∀ l (R : Partition n), Feasible Finset.univ l R → l ≤ k →
      ∃ S, Feasible Finset.univ k S ∧ cost d S ≤ cost d R) :
    cost d A ≤ cost d Q := by
  classical
  have hAT : A ∪ (O \ A) = O := Finset.union_sdiff_of_subset hA
  have hAdis : Disjoint A (O \ A) := disjoint_sdiff_self_right
  have hcard : A.card + (O \ A).card = k := by
    rw [← Finset.card_union_of_disjoint hAdis, hAT]
    exact hO.1.1
  obtain ⟨S, hS, hcostS⟩ := hrefine (j + (O \ A).card) (Q ∪ (O \ A))
    (splice_feasible hO.1 hA hQ) (by omega)
  have hcomp := (hO.2 S hS).trans hcostS
  have hcostO : cost d O = cost d A + cost d (O \ A) := by
    conv_lhs => rw [← hAT]
    unfold cost
    exact Finset.sum_union hAdis
  have hcostQ : cost d (Q ∪ (O \ A)) = cost d Q + cost d (O \ A) := by
    unfold cost
    exact Finset.sum_union (splice_disjoint hO.1 hA hQ)
  rw [hcostO, hcostQ] at hcomp
  linarith

lemma one_feasible {n : ℕ} {U : Cluster n} (hU : U.Nonempty) : Feasible U 1 {U} := by
  classical
  refine ⟨by simp, ?_, ?_, by simp⟩
  · intro C hC
    have heq : C = U := Finset.mem_singleton.mp hC
    simpa [heq] using hU
  · intro A hA B hB hAB
    have ha : A = U := Finset.mem_singleton.mp hA
    have hb : B = U := Finset.mem_singleton.mp hB
    exact False.elim (hAB (ha.trans hb.symm))

lemma two_feasible {n : ℕ} {M N : Cluster n}
    (hM : M.Nonempty) (hN : N.Nonempty) (hdis : Disjoint M N) :
    Feasible (M ∪ N) 2 {M, N} := by
  classical
  have hne : M ≠ N := by
    intro h
    obtain ⟨x, hx⟩ := hM
    exact Finset.disjoint_left.mp hdis hx (by simpa [← h] using hx)
  refine ⟨by simp [hne], ?_, ?_, by simp⟩
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl <;> assumption
  · intro A hA B hB hAB
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (hAB rfl)
    · exact hdis
    · exact hdis.symm
    · exact False.elim (hAB rfl)

lemma exists_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  classical
  obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  exact ⟨c, hc, by simpa [radius, hC] using he.symm⟩

lemma dist_le_radius {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c x : Point n} (hc : OptimalCenter d C c) (hx : x ∈ C) :
    d c x ≤ radius d C := by
  rw [← hc.2, eccentricity, dif_pos ⟨c, hc.1⟩]
  exact Finset.le_sup' _ hx

lemma radius_le_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {c : Point n} {a : ℝ} (hc : c ∈ C)
    (hbound : ∀ y ∈ C, d c y ≤ a) : radius d C ≤ a := by
  classical
  rw [radius, dif_pos ⟨c, hc⟩]
  apply (Finset.inf'_le _ hc).trans
  rw [eccentricity, dif_pos ⟨c, hc⟩]
  exact Finset.sup'_le _ _ hbound

end ContainedAux

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (O : Partition n) (hO : Optimal d Finset.univ k O) (x : Point n)
    (s : ℝ) (hs : 0 ≤ s) :
    (∑ C ∈ O.filter (fun C => C ⊆ ball d x s), radius d C) ≤ s := by
  classical
  let F := O.filter (fun C => C ⊆ ball d x s)
  change cost d F ≤ s
  by_cases hFn : F.Nonempty
  swap
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hFn
    simpa [cost, hFempty] using hs
  have hFO : F ⊆ O := Finset.filter_subset _ _
  have hFpos : 1 ≤ F.card := Finset.card_pos.mpr hFn
  have hrefine : ∀ l (R : Partition n), Feasible Finset.univ l R → l ≤ k →
      ∃ S, Feasible Finset.univ k S ∧ cost d S ≤ cost d R := by
    intro l R hR hl
    exact RefineAux.refine_partition d hd R hR hl hk.2
  have hdiag : ∀ y, d y y = 0 := by
    obtain ⟨m, hm⟩ := hd
    intro y
    rw [← hm y y]
    exact @dist_self _ m.toPseudoMetricSpace y
  have hFUbound : ∀ y ∈ F.biUnion id, d x y ≤ s := by
    intro y hy
    obtain ⟨C, hCF, hyC⟩ := Finset.mem_biUnion.mp hy
    have hsub : C ⊆ ball d x s := (Finset.mem_filter.mp hCF).2
    exact (Finset.mem_filter.mp (hsub hyC)).2
  have hxO : x ∈ O.biUnion id := by
    rw [hO.1.2.2.2]
    exact Finset.mem_univ x
  obtain ⟨B, hBO, hxB⟩ := Finset.mem_biUnion.mp hxO
  change x ∈ B at hxB
  by_cases hBF : B ∈ F
  · have hxF : x ∈ F.biUnion id := Finset.mem_biUnion.mpr ⟨B, hBF, hxB⟩
    have hreplace := ContainedAux.replacement_bound d hO hFO
      (ContainedAux.one_feasible ⟨x, hxF⟩) hFpos hrefine
    have hr := ContainedAux.radius_le_center d hxF hFUbound
    simpa [cost] using hreplace.trans (by simpa [cost] using hr)
  · obtain ⟨b, hb⟩ := ContainedAux.exists_center d (hO.1.2.1 B hBO)
    have hrB : 0 ≤ radius d B := by
      have h := ContainedAux.dist_le_radius hb hb.1
      rw [hdiag] at h
      exact h
    let A := insert B F
    have hAO : A ⊆ O := Finset.insert_subset hBO hFO
    have hAcost : cost d A = radius d B + cost d F := by
      simp [A, cost, hBF]
    have hAsize : 2 ≤ A.card := by
      simp only [A, Finset.card_insert_of_notMem hBF]
      omega
    by_cases hbx : b = x
    · have hxA : x ∈ A.biUnion id := Finset.mem_biUnion.mpr ⟨B, by simp [A], hxB⟩
      have hUbound : radius d (A.biUnion id) ≤ s + radius d B := by
        apply ContainedAux.radius_le_center d hxA
        intro y hy
        have hy' : y ∈ B ∪ F.biUnion id := by simpa [A] using hy
        rcases Finset.mem_union.mp hy' with hyB | hyF
        · have h := ContainedAux.dist_le_radius hb hyB
          rw [hbx] at h
          linarith
        · have h := hFUbound y hyF
          linarith
      have hreplace := ContainedAux.replacement_bound d hO hAO
        (ContainedAux.one_feasible ⟨x, hxA⟩) (by omega : 1 ≤ A.card) hrefine
      have hcomp : cost d A ≤ s + radius d B :=
        hreplace.trans (by simpa [cost] using hUbound)
      rw [hAcost] at hcomp
      linarith
    · let M := insert x (F.biUnion id)
      let N := B.erase x
      have hMn : M.Nonempty := ⟨x, Finset.mem_insert_self _ _⟩
      have hbN : b ∈ N := Finset.mem_erase.mpr ⟨hbx, hb.1⟩
      have hNn : N.Nonempty := ⟨b, hbN⟩
      have hBdis : Disjoint B (F.biUnion id) :=
        ContainedAux.outside_union_disjoint hO.1 hFO (Finset.mem_sdiff.mpr ⟨hBO, hBF⟩)
      have hMNdis : Disjoint M N := by
        apply Finset.disjoint_left.mpr
        intro y hyM hyN
        obtain ⟨hyx, hyB⟩ := Finset.mem_erase.mp hyN
        rcases Finset.mem_insert.mp hyM with hy | hyF
        · exact hyx hy
        · exact Finset.disjoint_left.mp hBdis hyB hyF
      have hMNunion : M ∪ N = A.biUnion id := by
        ext y
        by_cases hyx : y = x
        · subst y
          simp [M, N, A, hxB]
        · simp [M, N, A, hyx, or_assoc, or_left_comm, or_comm]
      have hQ : Feasible (A.biUnion id) 2 {M, N} := by
        rw [← hMNunion]
        exact ContainedAux.two_feasible hMn hNn hMNdis
      have hMrad : radius d M ≤ s := by
        apply ContainedAux.radius_le_center d (Finset.mem_insert_self x (F.biUnion id))
        intro y hy
        rcases Finset.mem_insert.mp hy with hyx | hyF
        · subst y
          simpa [hdiag] using hs
        · exact hFUbound y hyF
      have hNrad : radius d N ≤ radius d B := by
        apply ContainedAux.radius_le_center d hbN
        intro y hy
        exact ContainedAux.dist_le_radius hb (Finset.mem_erase.mp hy).2
      have hMNne : M ≠ N := by
        intro h
        obtain ⟨y, hy⟩ := hMn
        exact Finset.disjoint_left.mp hMNdis hy (by simpa [← h] using hy)
      have hQcost : cost d ({M, N} : Partition n) ≤ s + radius d B := by
        simp only [cost, Finset.mem_singleton, Finset.sum_insert (Finset.notMem_singleton.mpr hMNne),
          Finset.sum_singleton]
        exact add_le_add hMrad hNrad
      have hreplace := ContainedAux.replacement_bound d hO hAO hQ hAsize hrefine
      have hcomp := hreplace.trans hQcost
      rw [hAcost] at hcomp
      linarith
