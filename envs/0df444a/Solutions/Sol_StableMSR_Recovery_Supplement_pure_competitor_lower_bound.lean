-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.pure_competitor_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T16:15:36.312258+00:00
-- url     : https://prove2.me/submissions/0e3dfc79-d0e1-4f66-807f-705bf45f45b7

import Definitions.Def_StableMSR_Recovery_Supplement_Hub

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Supplement

private theorem add_block {n j : ℕ} {W C : Cluster n} {A : Partition n}
    (h : Feasible W j A) (hne : C.Nonempty) (hd : Disjoint C W) :
    C ∉ A ∧ Feasible (C ∪ W) (j+1) (insert C A) := by
  have hdB {B} (hB : B ∈ A) : Disjoint C B := by
    refine Finset.disjoint_left.mpr (fun {_} hx hy => Finset.disjoint_left.mp hd hx ?_)
    rw [← h.2.2.2]
    exact Finset.mem_biUnion.mpr ⟨B,hB,hy⟩
  have hout : C ∉ A := by
    intro hC
    obtain ⟨x,hx⟩ := hne
    exact Finset.disjoint_left.mp (hdB hC) hx hx
  refine ⟨hout, by simp [hout,h.1], ?_, ?_, by simp [h.2.2.2]⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hne
    · exact h.2.1 B hB
  · intro B hB D hD hBD
    by_cases hBC : B = C
    · subst B
      exact hdB ((Finset.mem_insert.mp hD).resolve_left (Ne.symm hBD))
    · have hBA := (Finset.mem_insert.mp hB).resolve_left hBC
      rcases Finset.mem_insert.mp hD with hDC | hDA
      · subst D
        exact (hdB hBA).symm
      · exact h.2.2.1 hBA hDA hBD

private theorem map_cost {n m : ℕ} (e : Point n ↪ Point m)
    (d : Point n → Point n → ℝ) (p : Point m → Point m → ℝ)
    (he : ∀ x y, p (e x) (e y) = d x y) (A : Partition n) :
    cost p (A.image (Finset.map e)) = cost d A := by
  unfold cost
  rw [Finset.sum_image (Finset.map_injective e).injOn]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : C.Nonempty
  · rw [radius, dif_pos hC.map, radius, dif_pos hC, Finset.inf'_map]
    apply Finset.inf'_congr _ rfl
    intro c _
    change eccentricity p (C.map e) (e c) = eccentricity d C c
    rw [eccentricity, dif_pos hC.map, eccentricity, dif_pos hC, Finset.sup'_map]
    exact Finset.sup'_congr _ rfl (fun x _ => he c x)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hC, radius]

private theorem singleton_partition {n : ℕ} (T : Cluster n) :
    Feasible T T.card (T.image (fun x => ({x} : Cluster n))) := by
  refine ⟨Finset.card_image_of_injective _ Finset.singleton_injective, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hC
    exact Finset.singleton_nonempty _
  · intro B hB C hC hne
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hC
    exact Finset.disjoint_singleton.mpr (fun h => hne (congrArg _ h))
  · ext x
    simp

private theorem source_bounds {n k : ℕ} (d : Point n → Point n → ℝ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray d) :
    0 ≤ optimumValue d k ∧ optimumValue d k ≤ diameter d Finset.univ ∧
    ∀ x y, d x y ≤ diameter d Finset.univ := by
  obtain ⟨m,hm⟩ := hd
  let _ : MetricSpace (Point n) := m
  have diag (x : Point n) : d x x = 0 := by rw [← hm]; exact dist_self _
  have bound (x y : Point n) : d x y ≤ diameter d Finset.univ := by
    have hn : (Finset.univ : Cluster n).Nonempty := ⟨x,Finset.mem_univ _⟩
    rw [diameter,dif_pos hn]
    refine le_trans ?_ (Finset.le_sup' (eccentricity d _) (Finset.mem_univ x))
    rw [eccentricity,dif_pos hn]
    exact Finset.le_sup' (d x) (Finset.mem_univ y)
  obtain ⟨T,_,hT⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Cluster n)) (n := k-1) (by simp; omega)
  have hC : Tᶜ.Nonempty := Finset.card_pos.mp (by rw [Finset.card_compl,hT]; simp; omega)
  let A := insert Tᶜ (T.image (fun x => ({x} : Cluster n)))
  obtain ⟨hout,hA⟩ := add_block (singleton_partition T) hC disjoint_compl_left
  have hAk : Feasible Finset.univ k A := by
    have hj : T.card+1 = k := by omega
    have cover : Tᶜ ∪ T = Finset.univ := by ext x; simp [em']
    simpa [A,hj,cover] using hA
  let F := (Finset.univ : Finset (Partition n)).filter (Feasible Finset.univ k)
  have hmem : A ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAk⟩
  have hF : F.Nonempty := ⟨A,hmem⟩
  have hv : optimumValue d k = F.inf' hF (cost d) := by simp [optimumValue,F,hF]
  rw [hv]
  refine ⟨Finset.le_inf' _ _ (fun Q _ => ?_),(Finset.inf'_le (cost d) hmem).trans ?_,bound⟩
  · apply Finset.sum_nonneg
    intro C _
    by_cases h : C.Nonempty
    · rw [radius,dif_pos h]
      apply Finset.le_inf'
      intro c hc
      rw [eccentricity,dif_pos h,← diag c]
      exact Finset.le_sup' (d c) hc
    · simp [radius,h]
  · change (∑ C ∈ insert Tᶜ _, radius d C) ≤ _
    rw [Finset.sum_insert hout, Finset.sum_eq_zero (fun B hB => ?_),add_zero]
    · have hn := hC
      obtain ⟨x,hx⟩ := hn
      rw [radius,dif_pos hC]
      refine (Finset.inf'_le _ hx).trans ?_
      rw [eccentricity,dif_pos hC]
      exact Finset.sup'_le _ _ (fun y _ => bound x y)
    · obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hB
      simp [radius,eccentricity,diag]

private theorem split_once {n j : ℕ} {A : Partition n} (d : Point n → Point n → ℝ)
    (diag : ∀ x, d x x = 0) (hA : Feasible Finset.univ j A) (hj : j < n) :
    ∃ B, Feasible Finset.univ (j+1) B ∧ cost d B ≤ cost d A := by
  have big : ∃ C ∈ A, 1 < C.card := by
    by_contra! h
    have hb := Finset.card_biUnion_le (s := A) (t := id)
    rw [hA.2.2.2] at hb
    have hsum := Finset.sum_le_sum h
    simp [hA.1] at hsum hb
    omega
  obtain ⟨C,hC,hbig⟩ := big
  have hCn := hA.2.1 C hC
  obtain ⟨c,hc,hcenter⟩ := Finset.exists_mem_eq_inf' hCn (eccentricity d C)
  have other : ∃ x ∈ C, x ≠ c := by
    obtain ⟨x,hx,y,hy,hne⟩ := Finset.one_lt_card.mp hbig
    by_cases h : x = c
    · exact ⟨y,hy,h ▸ Ne.symm hne⟩
    · exact ⟨x,hx,h⟩
  obtain ⟨x,hx,hxc⟩ := other
  let R := A.erase C
  let W := R.biUnion id
  have hR : Feasible W R.card R :=
    ⟨rfl,fun B hB => hA.2.1 B (Finset.mem_erase.mp hB).2,
      fun _ hB _ hV hne => hA.2.2.1 (Finset.mem_erase.mp hB).2 (Finset.mem_erase.mp hV).2 hne,rfl⟩
  have hdis : Disjoint C W := by
    apply (Finset.disjoint_biUnion_right _ _ _).mpr
    intro B hB
    exact hA.2.2.1 hC (Finset.mem_erase.mp hB).2 (Finset.mem_erase.mp hB).1.symm
  have hc' : c ∈ C.erase x := Finset.mem_erase.mpr ⟨hxc.symm,hc⟩
  obtain ⟨houtE,hE⟩ := add_block hR ⟨_,hc'⟩ (hdis.mono_left (Finset.erase_subset x C))
  have hdX : Disjoint ({x} : Cluster n) (C.erase x ∪ W) := by
    apply Finset.disjoint_singleton_left.mpr
    simpa using Finset.disjoint_left.mp hdis hx
  obtain ⟨houtX,hX⟩ := add_block hE (Finset.singleton_nonempty x) hdX
  have cover : {x} ∪ (C.erase x ∪ W) = Finset.univ := by
    have he : insert C R = A := Finset.insert_erase hC
    have cov := hA.2.2.2
    rw [←he,Finset.biUnion_insert] at cov
    change C ∪ W = _ at cov
    simpa [←Finset.union_assoc,Finset.insert_erase hx] using cov
  have hnum : R.card + 1 + 1 = j+1 := by
    have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨C,hC⟩)
    dsimp [R]
    rw [Finset.card_erase_of_mem hC,hA.1]
    rw [hA.1] at hpos
    omega
  have radle : radius d (C.erase x) ≤ radius d C := by
    rw [radius,dif_pos (show (C.erase x).Nonempty from ⟨_,hc'⟩),radius,dif_pos hCn,hcenter]
    refine (Finset.inf'_le _ hc').trans ?_
    rw [eccentricity,dif_pos (show (C.erase x).Nonempty from ⟨_,hc'⟩),eccentricity,dif_pos hCn]
    exact Finset.sup'_le _ _ (fun y hy => Finset.le_sup' _ (Finset.mem_erase.mp hy).2)
  refine ⟨_,by simpa only [cover,hnum] using hX,?_⟩
  change (∑ B ∈ insert {x} (insert (C.erase x) R), radius d B) ≤ ∑ B ∈ A, radius d B
  rw [Finset.sum_insert houtX,Finset.sum_insert houtE,← Finset.sum_erase_add _ _ hC]
  have single : radius d {x} = 0 := by simp [radius,eccentricity,diag]
  rw [single,zero_add]
  change _ ≤ (∑ B ∈ R, radius d B) + radius d C
  linarith

private theorem optimum_le_partition {n k j : ℕ} (d : Point n → Point n → ℝ)
    (diag : ∀ x, d x x = 0) (hkn : k ≤ n) (hjk : j ≤ k)
    {A : Partition n} (hA : Feasible Finset.univ j A) : optimumValue d k ≤ cost d A := by
  by_cases eq : j = k
  · subst j
    let F := (Finset.univ : Finset (Partition n)).filter (Feasible Finset.univ k)
    have hmem : A ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA⟩
    have hF : F.Nonempty := ⟨A,hmem⟩
    have hv : optimumValue d k = F.inf' hF (cost d) := by simp [optimumValue,F,hF]
    rw [hv]
    exact Finset.inf'_le _ hmem
  · obtain ⟨B,hB,hBA⟩ := split_once d diag hA (by omega)
    exact (optimum_le_partition d diag hkn (show j+1 ≤ k by omega) hB).trans hBA
termination_by k-j
decreasing_by omega

theorem solution {n k : ℕ} (d : Point n → Point n → ℝ) (γ τ : ℝ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray d)
    (hD : diameter d Finset.univ < hubRadius d γ τ)
    (hδ : hubRadius d γ τ < dummyDistance d γ τ)
    (Q : Partition (n+k+2)) (hQ : Feasible Finset.univ (k+2) Q)
    (hne : Q ≠ suppliedPartition n k)
    (hpure : ∀ C ∈ Q, C ⊆ hubSource n k ∨ ∀ x ∈ C, n < x.val) :
    dummyDistance d γ τ + optimumValue d k ≤ cost (hubDistance d k γ τ) Q := by
  let N := n+k+2
  let dp := hubDistance d k γ τ
  let X := hubSource n k
  let Z := (Finset.univ : Cluster N).filter (fun x => n < x.val)
  let S := Z.image (fun x => ({x} : Cluster N))
  let u : Point N := ⟨n,by dsimp [N]; omega⟩
  let e : Point n ↪ Point N := ⟨fun x => ⟨x.val,by dsimp [N]; omega⟩,
    fun _ _ h => Fin.ext (congrArg (fun z : Point N => z.val) h)⟩
  have memX (x : Point N) : x ∈ X ↔ x.val ≤ n := by simp [X,hubSource]
  have memZ (x : Point N) : x ∈ Z ↔ n < x.val := by simp [Z]
  have cover (x : Point N) : ∃ C ∈ Q, x ∈ C := by
    have hx : x ∈ Q.biUnion id := hQ.2.2.2 ▸ Finset.mem_univ _
    exact Finset.mem_biUnion.mp hx
  have unique {C B : Cluster N} (hC : C ∈ Q) (hB : B ∈ Q) {x}
      (hxC : x ∈ C) (hxB : x ∈ B) : C = B := by
    by_contra ne
    exact Finset.disjoint_left.mp (hQ.2.2.1 hC hB ne) hxC hxB
  obtain ⟨H,hH,huH⟩ := cover u
  have hHX : H ⊆ X := (hpure H hH).resolve_right (fun h => (lt_irrefl n) (h u huH))
  have hHout : H ∉ S := by
    intro h
    obtain ⟨z,hz,hzH⟩ := Finset.mem_image.mp h
    have eq : u = z := Finset.mem_singleton.mp (hzH.symm ▸ huH)
    subst z
    exact (lt_irrefl n) ((memZ _).1 hz)
  let f (i : Fin (k+1)) : Point N := ⟨n+1+i.val,by dsimp [N]; omega⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [f] at this
    omega
  have him : Z = Finset.univ.image f := by
    ext x
    rw [memZ,Finset.mem_image]
    constructor
    · intro h
      refine ⟨⟨x.val-(n+1),by dsimp [N] at x; omega⟩,Finset.mem_univ _,Fin.ext ?_⟩
      dsimp [f]; omega
    · rintro ⟨i,_,rfl⟩; dsimp [f]; omega
  have hSz : S.card = k+1 := by
    change (Z.image _).card = _
    rw [Finset.card_image_of_injective _ Finset.singleton_injective,him,
      Finset.card_image_of_injective _ hf]; simp
  have nonsingle : ∃ B ∈ Q, B ⊆ Z ∧ 1 < B.card := by
    by_contra! no
    have Ssub : S ⊆ Q := by
      intro B hB
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨C,hC,hzC⟩ := cover z
      have hz' := (memZ _).1 hz
      have hcz : C ⊆ Z := fun x hx => (memZ _).2
        (((hpure _ hC).resolve_left (fun h => (not_lt_of_ge ((memX _).1 (h hzC))) hz')) _ hx)
      have eq : C = {z} := by
        ext x
        exact ⟨fun hx => Finset.mem_singleton.mpr (Finset.card_le_one.mp (no C hC hcz) x hx z hzC),
          fun hx => Finset.mem_singleton.mp hx ▸ hzC⟩
      exact eq ▸ hC
    have subs : insert H S ⊆ Q := Finset.insert_subset hH Ssub
    have eqQ : insert H S = Q := Finset.eq_of_subset_of_card_le subs
      (by rw [Finset.card_insert_of_notMem hHout,hSz,hQ.1])
    have eqX : H = X := Finset.Subset.antisymm hHX (by
      intro x hx
      obtain ⟨B,hB,hxB⟩ := cover x
      rw [←eqQ] at hB
      rcases Finset.mem_insert.mp hB with rfl | hs
      · exact hxB
      · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
        have xz := Finset.mem_singleton.mp hxB
        subst z
        exact False.elim ((not_lt_of_ge ((memX _).1 hx)) ((memZ _).1 hz)))
    exact hne (eqQ.symm.trans (congrArg (fun B => insert B S) eqX))
  obtain ⟨B,hB,hBZ,hbig⟩ := nonsingle
  have hBH : B ≠ H := by
    intro eq
    have huZ := hBZ (eq.symm ▸ huH)
    exact (lt_irrefl n) ((memZ _).1 huZ)
  obtain ⟨ha0,haD,bd⟩ := source_bounds d hk hkn hd
  have hR := lt_of_le_of_lt (ha0.trans haD) hD
  have hδ0 := hR.trans hδ
  have hL : 0 < crossDistance d γ τ := by unfold crossDistance; linarith
  obtain ⟨m,hm⟩ := hd
  let _ : MetricSpace (Point n) := m
  have diag (x : Point n) : d x x = 0 := (hm x x).symm.trans (dist_self _)
  have d0 (x y : Point n) : 0 ≤ d x y := by rw [←hm]; exact dist_nonneg
  have dp0 (x y : Point N) : 0 ≤ dp x y := by
    unfold dp hubDistance
    split_ifs <;> first | exact le_rfl | apply d0 | linarith
  have rad0 (C : Cluster N) : 0 ≤ radius dp C := by
    by_cases hn : C.Nonempty
    · rw [radius,dif_pos hn]
      apply Finset.le_inf'
      intro c hc
      rw [eccentricity,dif_pos hn]
      exact (dp0 c c).trans (Finset.le_sup' _ hc)
    · simp [radius,hn]
  have radB : dummyDistance d γ τ ≤ radius dp B := by
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hbig
    have hn : B.Nonempty := ⟨_,hx⟩
    rw [radius,dif_pos hn]
    apply Finset.le_inf'
    intro c hc
    obtain ⟨z,hz,hcz⟩ : ∃ z ∈ B, c ≠ z := by
      by_cases eq : c = x
      · exact ⟨y,hy,eq ▸ hxy⟩
      · exact ⟨x,hx,eq⟩
    have hc' := (memZ _).1 (hBZ hc)
    have hz' := (memZ _).1 (hBZ hz)
    have val : dp c z = dummyDistance d γ τ := by
      simp [dp,hubDistance,hcz,not_lt.mpr hc'.le,not_lt.mpr hz'.le,ne_of_gt hc',ne_of_gt hz']
    rw [eccentricity,dif_pos hn,← val]
    exact Finset.le_sup' _ hz
  have hubval (x : Point N) (hx : x.val < n) :
      dp u x = hubRadius d γ τ ∧ dp x u = hubRadius d γ τ := by
    have ne : x ≠ u := by intro eq; subst x; exact (lt_irrefl n) hx
    simp [dp,hubDistance,ne,ne.symm,hx,u]
  by_cases isolated : H = {u}
  · let A := (Finset.univ : Finset (Cluster n)).filter (fun C => C.map e ∈ Q)
    let F := A.image (Finset.map e)
    have memA (C : Cluster n) : C ∈ A ↔ C.map e ∈ Q := by simp [A]
    have small {C : Cluster n} {x : Point N} (hx : x ∈ C.map e) : x.val < n := by
      obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
      exact y.isLt
    have hFQ : F ⊆ Q := by
      intro C hC
      obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hC
      exact (memA _).1 hV
    have allsrc {V : Cluster N} (hV : V ∈ Q) {y : Fin n} (he : e y ∈ V) :
        ∀ z ∈ V, z.val < n := by
      have hVX : V ⊆ X := (hpure _ hV).resolve_right (fun h => (not_lt_of_ge y.isLt.le) (h _ he))
      intro z hz
      refine lt_of_le_of_ne ((memX _).1 (hVX hz)) (fun eq => ?_)
      have huV : u ∈ V := (show z = u from Fin.ext eq) ▸ hz
      have hVH := unique hV hH huV huH
      have eyu : e y = u := Finset.mem_singleton.mp ((hVH.trans isolated) ▸ he)
      have hv := congrArg Fin.val eyu
      exact (Nat.ne_of_lt y.isLt) hv
    have hA : Feasible Finset.univ A.card A := by
      refine ⟨rfl,?_,?_,?_⟩
      · intro C hC
        obtain ⟨z,hz⟩ := hQ.2.1 _ ((memA _).1 hC)
        obtain ⟨x,hx,_⟩ := Finset.mem_map.mp hz
        exact ⟨x,hx⟩
      · intro C hC V hV ne
        exact (Finset.disjoint_map e).1 (hQ.2.2.1 ((memA _).1 hC) ((memA _).1 hV)
          (fun eq => ne (Finset.map_injective e eq)))
      · apply Finset.eq_univ_of_forall
        intro y
        obtain ⟨V,hV,hyV⟩ := cover (e y)
        let C := (Finset.univ : Cluster n).filter (fun x => e x ∈ V)
        have eq : C.map e = V := by
          ext z
          constructor
          · intro hz
            obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hz
            exact (Finset.mem_filter.mp hx).2
          · intro hz
            let a : Fin n := ⟨z.val,allsrc hV hyV z hz⟩
            have ea : e a = z := Fin.ext rfl
            exact Finset.mem_map.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ea.symm ▸ hz⟩,ea⟩
        exact Finset.mem_biUnion.mpr ⟨C,(memA _).2 (eq.symm ▸ hV),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hyV⟩⟩
    have outH : H ∉ F := by
      intro h
      obtain ⟨C,_,eq⟩ := Finset.mem_image.mp h
      exact (lt_irrefl n) (small (eq.symm ▸ huH))
    have outB : B ∉ F := by
      intro h
      obtain ⟨C,_,eq⟩ := Finset.mem_image.mp h
      obtain ⟨z,hz⟩ := hQ.2.1 B hB
      exact (not_lt_of_ge ((memZ _).1 (hBZ hz)).le) (small (eq.symm ▸ hz))
    have subB : insert B F ⊆ Q := Finset.insert_subset hB hFQ
    have subHB : insert H (insert B F) ⊆ Q := Finset.insert_subset hH subB
    have hj : A.card ≤ k := by
      have hcard := Finset.card_le_card subHB
      rw [Finset.card_insert_of_notMem (by simpa using And.intro hBH.symm outH),
        Finset.card_insert_of_notMem outB,hQ.1] at hcard
      change (A.image (Finset.map e)).card + 1 + 1 ≤ _ at hcard
      rw [Finset.card_image_of_injective _ (Finset.map_injective e)] at hcard
      omega
    have psrc (x y : Fin n) : dp (e x) (e y) = d x y := by
      by_cases eq : x = y
      · subst y
        simp [dp,hubDistance,diag]
      · have neq : e x ≠ e y := fun h => eq (e.injective h)
        have hx : (e x).val < n := x.isLt
        have hy : (e y).val < n := y.isLt
        simp only [dp,hubDistance,if_neg neq,dif_pos hx,dif_pos hy]
        rfl
    have lb := optimum_le_partition d diag hkn hj hA
    have total := Finset.sum_le_sum_of_subset_of_nonneg subB (fun C _ _ => rad0 C)
    rw [Finset.sum_insert outB] at total
    change radius dp B + cost dp F ≤ cost dp Q at total
    rw [show cost dp F = cost d A from map_cost e d dp psrc A] at total
    exact (add_le_add radB lb).trans total
  · have has : ∃ y ∈ H, y ≠ u := by
      by_contra! no
      exact isolated (Finset.Subset.antisymm (fun i hi => Finset.mem_singleton.mpr (no i hi))
        (Finset.singleton_subset_iff.mpr huH))
    obtain ⟨y,hy,hyu⟩ := has
    have lt_src {x : Point N} (hx : x ∈ H) (ne : x ≠ u) : x.val < n :=
      lt_of_le_of_ne ((memX _).1 (hHX hx)) (fun h => ne (Fin.ext h))
    have radH : hubRadius d γ τ ≤ radius dp H := by
      have hn : H.Nonempty := ⟨u,huH⟩
      rw [radius,dif_pos hn]
      apply Finset.le_inf'
      intro c hc
      rw [eccentricity,dif_pos hn]
      by_cases eq : c = u
      · subst c
        exact (hubval _ (lt_src hy hyu)).1 ▸ Finset.le_sup' (dp u) hy
      · exact (hubval _ (lt_src hc eq)).2 ▸ Finset.le_sup' (dp c) huH
    have sub : insert B {H} ⊆ Q := Finset.insert_subset hB (Finset.singleton_subset_iff.mpr hH)
    have sumle := Finset.sum_le_sum_of_subset_of_nonneg sub (fun C _ _ => rad0 C)
    rw [Finset.sum_insert (by simpa using hBH),Finset.sum_singleton] at sumle
    exact (add_le_add radB ((haD.trans hD.le).trans radH)).trans sumle
