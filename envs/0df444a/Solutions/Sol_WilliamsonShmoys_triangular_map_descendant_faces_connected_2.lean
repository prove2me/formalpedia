-- Prove2me | solution 2 for WilliamsonShmoys.triangular_map_descendant_faces_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:42:23.89063+00:00
-- url     : https://prove2.me/submissions/a79e6dea-b07a-453c-83c9-1e85bc41247f

import Definitions.Def_WilliamsonShmoys_TriangularMap

open SimpleGraph Finset

namespace S175T

variable {V F : Type} [Fintype V] [Fintype F] {H : SimpleGraph V}

def face (M : WilliamsonShmoys.TriangularMap H F) (d : H.Dart) : F := (M.dart.symm d).1

def rot (M : WilliamsonShmoys.TriangularMap H F) (a : H.Dart) : H.Dart :=
  M.dart ((M.dart.symm a.symm).1, (M.dart.symm a.symm).2 + 1)

lemma face_rot (M : WilliamsonShmoys.TriangularMap H F) (a : H.Dart) :
    face M (rot M a) = face M a.symm := by
  simp [face, rot]

lemma face_dart (M : WilliamsonShmoys.TriangularMap H F) (f : F) (i : Fin 3) :
    face M (M.dart (f, i)) = f := by
  simp [face]

lemma rot_fst (M : WilliamsonShmoys.TriangularMap H F) (a : H.Dart) :
    (rot M a).fst = a.fst := by
  unfold rot
  rw [M.dart_tail]
  have h := M.dart_head (M.dart.symm a.symm).1 (M.dart.symm a.symm).2
  simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h
  rw [← h]
  simp

lemma rot_injective (M : WilliamsonShmoys.TriangularMap H F) : Function.Injective (rot M) := by
  intro a b h
  unfold rot at h
  have h' := M.dart.injective h
  simp only [Prod.mk.injEq, add_left_inj] at h'
  have h2 : M.dart.symm a.symm = M.dart.symm b.symm := Prod.ext h'.1 h'.2
  have h3 := M.dart.symm.injective h2
  simpa using congrArg Dart.symm h3


lemma face_fst (M : WilliamsonShmoys.TriangularMap H F) (d : H.Dart) :
    ∃ i, M.corner (face M d) i = d.fst := by
  refine ⟨(M.dart.symm d).2, ?_⟩
  have h := M.dart_tail (M.dart.symm d).1 (M.dart.symm d).2
  simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h
  exact h.symm

lemma face_snd (M : WilliamsonShmoys.TriangularMap H F) (d : H.Dart) :
    ∃ i, M.corner (face M d) i = d.snd := by
  refine ⟨(M.dart.symm d).2 + 1, ?_⟩
  have h := M.dart_head (M.dart.symm d).1 (M.dart.symm d).2
  simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h
  exact h.symm

open Classical in
lemma parity (M : WilliamsonShmoys.TriangularMap H F) (X : Set F) (x : V) :
    Even ((univ.filter (fun a : H.Dart => a.fst = x ∧
      ¬ (face M a ∈ X ↔ face M a.symm ∈ X))).card) := by
  classical
  let Dx : Finset H.Dart := univ.filter (fun a => a.fst = x)
  let bnd : H.Dart → Prop := fun a => ¬ (face M a ∈ X ↔ face M a.symm ∈ X)
  have he : (univ.filter (fun a : H.Dart => a.fst = x ∧ bnd a)) = Dx.filter bnd := by
    ext a; simp [Dx]
  change Even ((univ.filter (fun a : H.Dart => a.fst = x ∧ bnd a)).card)
  rw [he]
  let χ : H.Dart → ZMod 2 := fun a => if face M a ∈ X then 1 else 0
  have hb_ind : ∀ a, (if bnd a then (1 : ZMod 2) else 0) = χ a + χ (rot M a) := by
    intro a
    simp only [bnd, χ, face_rot]
    by_cases h1 : face M a ∈ X <;> by_cases h2 : face M a.symm ∈ X <;> simp [h1, h2] <;> decide
  have hsum : ∑ a ∈ Dx, χ (rot M a) = ∑ a ∈ Dx, χ a := by
    refine Finset.sum_nbij (rot M) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro a ha
      simp only [Dx, mem_filter, mem_univ, true_and] at ha ⊢
      rw [rot_fst, ha]
    · intro a _ b _ h; exact rot_injective M h
    · intro b hb
      simp only [Dx, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hb
      obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp (rot_injective M)) b
      refine ⟨a, ?_, ha⟩
      simp only [Dx, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      rw [← rot_fst M a, ha, hb]
  have hcast : ((Dx.filter bnd).card : ZMod 2) = 0 := by
    rw [Finset.natCast_card_filter, Finset.sum_congr rfl (fun a _ => hb_ind a),
      Finset.sum_add_distrib, hsum, ← two_mul]
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_mul]
  exact (ZMod.natCast_eq_zero_iff_even).mp hcast

lemma no_even_forest {R B : SimpleGraph V} [DecidableRel B.Adj] (hR : R.IsAcyclic)
    (hBR : ∀ x y, B.Adj x y → R.Adj x y) (heven : ∀ x, Even (B.degree x)) :
    ∀ u v, ¬ B.Adj u v := by
  classical
  intro u v huv
  have hRuv := hBR u v huv
  have hbr : R.IsBridge s(u, v) := isAcyclic_iff_forall_adj_isBridge.mp hR hRuv
  rw [isBridge_iff] at hbr
  set S : Set V := {w | (R.deleteEdges {s(u, v)}).Reachable u w} with hS
  have huS : u ∈ S := Reachable.refl u
  have hvS : v ∉ S := hbr
  have hcross : ∀ x y, x ∈ S → y ∉ S → B.Adj x y → x = u ∧ y = v := by
    intro x y hx hy hxy
    have hRxy := hBR x y hxy
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.mp he with h | h
      · exact h
      · exact absurd (h.1 ▸ hx) hvS
    · exfalso; apply hy
      have : (R.deleteEdges {s(u, v)}).Adj x y := by
        rw [deleteEdges_adj]; exact ⟨hRxy, by simpa using he⟩
      exact Reachable.trans hx this.reachable
  let B' : SimpleGraph V :=
    { Adj := fun x y => B.Adj x y ∧ x ∈ S ∧ y ∈ S
      symm := ⟨by rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩⟩
      loopless := ⟨fun x hx => B.loopless.irrefl x hx.1⟩ }
  have hodd : ∀ x, Odd (B'.degree x) ↔ x = u := by
    intro x
    by_cases hx : x ∈ S
    · have hsplit := Finset.card_filter_add_card_filter_not (s := B.neighborFinset x)
        (p := fun y => y ∈ S)
      have hin : (B.neighborFinset x).filter (fun y => y ∈ S) = B'.neighborFinset x := by
        ext y; simp [B', hx]
      have hout : (B.neighborFinset x).filter (fun y => y ∉ S) =
          if x = u then {v} else ∅ := by
        ext y
        simp only [mem_filter, mem_neighborFinset]
        constructor
        · rintro ⟨hxy, hy⟩
          obtain ⟨rfl, rfl⟩ := hcross x y hx hy hxy
          simp
        · intro hy
          split_ifs at hy with hxu
          · rw [mem_singleton] at hy; subst hy; subst hxu; exact ⟨huv, hvS⟩
          · simp at hy
      rw [hin, hout, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hsplit
      have he := heven x
      split_ifs at hsplit with hxu
      · simp only [card_singleton] at hsplit
        simp only [hxu, iff_true]
        subst hxu
        rcases he with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      · simp only [card_empty, add_zero] at hsplit
        rw [hsplit]
        simp only [hxu, iff_false, Nat.not_odd_iff_even]
        exact he
    · have : B'.degree x = 0 := by
        rw [← card_neighborFinset_eq_degree, card_eq_zero]
        ext y; simp [B', hx]
      rw [this]
      simp only [Nat.not_odd_zero, false_iff]
      rintro rfl; exact hx huS
  have hcard := B'.even_card_odd_degree_vertices
  have : (univ.filter fun x => Odd (B'.degree x)) = {u} := by
    ext x; simp [hodd]
  rw [this, card_singleton] at hcard
  exact Nat.not_even_one hcard

end S175T

open S175T in
theorem solution
    {V F : Type} [Fintype V] [Fintype F]
    {H : SimpleGraph V} (M : WilliamsonShmoys.TriangularMap H F)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree)
    (root : V) (Q : (v : V) → R.Walk root v)
    (hQ : ∀ v, (Q v).IsPath) (v : V) :
    ((M.cotree R).induce
      {f : F | ∃ i : Fin 3, v ∈ (Q (M.corner f i)).support}).Connected := by
  classical
  set T : Set V := {w | v ∈ (Q w).support} with hT
  set SF : Set F := {f : F | ∃ i : Fin 3, v ∈ (Q (M.corner f i)).support} with hSFdef
  have huniq : ∀ w (p : R.Walk root w), p.IsPath → p = Q w := fun w p hp =>
    congrArg Subtype.val (hR.IsAcyclic.path_unique ⟨p, hp⟩ ⟨Q w, hQ w⟩)
  have hL2 : ∀ x y, R.Adj x y → y ∈ T → x ∉ T → y = v := by
    intro x y hxy hy hx
    by_cases hyx : y ∈ (Q x).support
    · exfalso; apply hx
      have h1 := huniq y ((Q x).takeUntil y hyx) ((hQ x).takeUntil hyx)
      have hsub := (Q x).support_takeUntil_subset_support hyx
      rw [h1] at hsub
      exact hsub hy
    · have h1 := huniq y ((Q x).concat hxy) ((hQ x).concat hyx hxy)
      have hs : v ∈ ((Q x).concat hxy).support := by rw [h1]; exact hy
      rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hs
      rcases hs with h | h
      · exact absurd h hx
      · exact h.symm
  have hpar : ∀ x x', R.Adj x v → x ∉ T → R.Adj x' v → x' ∉ T → x = x' := by
    intro x x' hx hxT hx' hx'T
    have h1 := huniq v ((Q x).concat hx) ((hQ x).concat hxT hx)
    have h2 := huniq v ((Q x').concat hx') ((hQ x').concat hx'T hx')
    obtain ⟨he, _⟩ := SimpleGraph.Walk.concat_inj (h1.trans h2.symm)
    exact he
  have hL1 : ∀ w, w ≠ root → R.Adj (Q w).penultimate w ∧
      (Q w).support = (Q (Q w).penultimate).support ++ [w] ∧
      (Q (Q w).penultimate).length < (Q w).length := by
    intro w hw
    have hnil : ¬ (Q w).Nil := fun h => hw h.eq.symm
    have hd := huniq _ (Q w).dropLast (hQ w).dropLast
    refine ⟨SimpleGraph.Walk.adj_penultimate hnil, ?_, ?_⟩
    · rw [← hd, SimpleGraph.Walk.support_dropLast_concat hnil]
    · rw [← hd]; have := SimpleGraph.Walk.length_dropLast_add_one hnil; omega
  have hSFne : Nonempty SF := by
    obtain ⟨f, i, hfi⟩ := M.vertex_covered v
    exact ⟨⟨f, i, by rw [hfi]; exact (Q v).end_mem_support⟩⟩
  refine ⟨?_⟩
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  by_contra hfg
  set G' := (M.cotree R).induce SF with hG'
  set X : Set F := {h | ∃ hh : h ∈ SF, G'.Reachable ⟨f, hf⟩ ⟨h, hh⟩} with hX
  let bnd : H.Dart → Prop := fun a => ¬ (face M a ∈ X ↔ face M a.symm ∈ X)
  have bnd_symm : ∀ a, bnd a → bnd a.symm := by
    intro a ha
    simp only [bnd, Dart.symm_symm] at ha ⊢
    tauto
  have hSF : ∀ d : H.Dart, (d.fst ∈ T ∨ d.snd ∈ T) → face M d ∈ SF ∧ face M d.symm ∈ SF := by
    intro d hd
    obtain ⟨i1, h1⟩ := face_fst M d
    obtain ⟨i2, h2⟩ := face_snd M d
    obtain ⟨i3, h3⟩ := face_fst M d.symm
    obtain ⟨i4, h4⟩ := face_snd M d.symm
    simp only [Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap] at h3 h4
    rcases hd with hd | hd
    · exact ⟨⟨i1, by rw [h1]; exact hd⟩, ⟨i4, by rw [h4]; exact hd⟩⟩
    · exact ⟨⟨i2, by rw [h2]; exact hd⟩, ⟨i3, by rw [h3]; exact hd⟩⟩
  let Bd : SimpleGraph V :=
    { Adj := fun x y => ∃ h : H.Adj x y, (x ∈ T ∨ y ∈ T) ∧ bnd ⟨(x, y), h⟩
      symm := ⟨by rintro x y ⟨h, ht, hb⟩; exact ⟨h.symm, ht.symm, bnd_symm _ hb⟩⟩
      loopless := ⟨fun x hx => H.loopless.irrefl x hx.1⟩ }
  have hBR : ∀ x y, Bd.Adj x y → R.Adj x y := by
    rintro x y ⟨h, ht, hb⟩
    by_contra hRxy
    let d : H.Dart := ⟨(x, y), h⟩
    obtain ⟨hs1, hs2⟩ := hSF d ht
    have hne : face M d ≠ face M d.symm := by
      intro he; exact hb (by rw [he])
    have hadj : G'.Adj ⟨face M d, hs1⟩ ⟨face M d.symm, hs2⟩ := ⟨hne, d, hRxy, rfl, rfl⟩
    apply hb
    constructor
    · rintro ⟨_, hr⟩; exact ⟨hs2, hr.trans hadj.reachable⟩
    · rintro ⟨_, hr⟩; exact ⟨hs1, hr.trans hadj.symm.reachable⟩
  have hevenT : ∀ x ∈ T, Even (Bd.degree x) := by
    intro x hxT
    have hdeg : Bd.degree x =
        (univ.filter (fun a : H.Dart => a.fst = x ∧ bnd a)).card := by
      rw [← card_neighborFinset_eq_degree]
      symm
      refine Finset.card_nbij (fun a => a.snd) ?_ ?_ ?_
      · intro a ha
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha
        obtain ⟨hax, hab⟩ := ha
        rw [mem_coe, mem_neighborFinset]
        obtain ⟨⟨x', y⟩, hadj⟩ := a
        simp only at hax
        subst hax
        exact ⟨hadj, Or.inl hxT, hab⟩
      · intro a ha b hb hab
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha hb
        apply Dart.ext
        exact Prod.ext (ha.1.trans hb.1.symm) hab
      · intro y hy
        rw [mem_coe, mem_neighborFinset] at hy
        obtain ⟨h, _, hb⟩ := hy
        refine ⟨⟨(x, y), h⟩, ?_, rfl⟩
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
        first | exact ⟨rfl, hb⟩ | exact hb
    rw [hdeg]
    convert parity M X x
  have hnbr : ∀ x, x ∉ T → ∀ y, Bd.Adj x y → y = v := by
    intro x hx y hxy
    have hy : y ∈ T := by
      obtain ⟨_, ht, _⟩ := hxy
      exact ht.resolve_left hx
    exact hL2 x y (hBR x y hxy) hy hx
  have heven : ∀ x, Even (Bd.degree x) := by
    have hO : (univ.filter fun x => Odd (Bd.degree x)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      have key : ∀ c, Odd (Bd.degree c) → c ∉ T ∧ Bd.Adj c v := by
        intro c hc
        have hcT : c ∉ T := fun h => (Nat.not_even_iff_odd.mpr hc) (hevenT c h)
        refine ⟨hcT, ?_⟩
        have hpos : 0 < Bd.degree c := hc.pos
        rw [← card_neighborFinset_eq_degree, Finset.card_pos] at hpos
        obtain ⟨y, hy⟩ := hpos
        rw [mem_neighborFinset] at hy
        have := hnbr c hcT y hy
        rw [this] at hy; exact hy
      obtain ⟨haT, hav⟩ := key a ha
      obtain ⟨hbT, hbv⟩ := key b hb
      exact hpar a b (hBR _ _ hav) haT (hBR _ _ hbv) hbT
    have hE : Even (univ.filter fun x => Odd (Bd.degree x)).card := by
      convert Bd.even_card_odd_degree_vertices
    have h0 : (univ.filter fun x => Odd (Bd.degree x)).card = 0 := by
      rcases hE with ⟨k, hk⟩; omega
    intro x
    by_contra hx
    rw [Nat.not_even_iff_odd] at hx
    rw [Finset.card_eq_zero] at h0
    have : x ∈ (univ.filter fun x => Odd (Bd.degree x)) := by simp [hx]
    rw [h0] at this; simp at this
  have hno := no_even_forest (B := Bd) hR.IsAcyclic hBR (fun x => by convert heven x)
  have hnb : ∀ a : H.Dart, a.fst ∈ T → (face M a ∈ X ↔ face M a.symm ∈ X) := by
    intro a ha
    by_contra hb
    exact hno a.fst a.snd ⟨a.adj, Or.inl ha, hb⟩
  have hit : ∀ k a, a.fst ∈ T → (face M ((rot M)^[k] a) ∈ X ↔ face M a ∈ X) := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ha
      rw [Function.iterate_succ_apply', face_rot]
      have hfst : ((rot M)^[k] a).fst = a.fst := by
        clear ih
        induction k with
        | zero => rfl
        | succ k ih2 => rw [Function.iterate_succ_apply', rot_fst, ih2]
      rw [← ih a ha]
      exact (hnb _ (by rw [hfst]; exact ha)).symm
  have hvert : ∀ a b : H.Dart, a.fst = b.fst → a.fst ∈ T → (face M a ∈ X ↔ face M b ∈ X) := by
    intro a b hab ha
    obtain ⟨k, hk⟩ := M.rotation_transitive a b hab
    have hk' : (rot M)^[k] a = b := hk
    rw [← hk', hit k a ha]
  let cls : V → Prop := fun w => ∀ a : H.Dart, a.fst = w → face M a ∈ X
  have hcls : ∀ (d : H.Dart), d.fst ∈ T → (cls d.fst ↔ face M d ∈ X) := by
    intro d hd
    constructor
    · intro h; exact h d rfl
    · intro h a ha; exact (hvert d a ha.symm hd).mp h
  have hedge : ∀ x w (h : H.Adj x w), x ∈ T → w ∈ T → (cls x ↔ cls w) := by
    intro x w h hx hw
    let d : H.Dart := ⟨(x, w), h⟩
    have e1 := hcls d hx
    have e2 := hcls d.symm (by simpa [d] using hw)
    have e3 := hnb d hx
    simp only [d] at e1 e2 e3
    exact e1.trans (e3.trans e2.symm)
  have hall : ∀ n w, (Q w).length = n → w ∈ T → (cls w ↔ cls v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hlen hw
      by_cases hwv : w = v
      · rw [hwv]
      have hwr : w ≠ root := by
        intro h
        apply hwv
        have hw' := hw
        simp only [hT, Set.mem_setOf_eq] at hw'
        subst h
        rw [SimpleGraph.Walk.isPath_iff_eq_nil.mp (hQ w)] at hw'
        simp at hw'
        first | exact hw'.symm | exact hw'
      obtain ⟨hadj, hsupp, hlt⟩ := hL1 w hwr
      have hxT : (Q w).penultimate ∈ T := by
        have hw' : v ∈ (Q w).support := hw
        rw [hsupp, List.mem_append, List.mem_singleton] at hw'
        rcases hw' with h | h
        · exact h
        · exact absurd h.symm hwv
      exact (hedge _ _ (hRH hadj) hxT hw).symm.trans (ih _ (hlen ▸ hlt) _ rfl hxT)
  obtain ⟨i, hi⟩ := hf
  obtain ⟨j, hj⟩ := hg
  have hcf : cls (M.corner f i) := by
    intro a ha
    have h1 := M.dart_tail f i
    refine (hvert (M.dart (f, i)) a (by rw [h1, ha]) (by rw [h1]; exact hi)).mp ?_
    rw [face_dart]
    exact ⟨⟨i, hi⟩, Reachable.refl _⟩
  have hcv := (hall _ _ rfl hi).mp hcf
  have hcg := (hall _ _ rfl hj).mpr hcv
  have := hcg (M.dart (g, j)) (M.dart_tail g j)
  rw [face_dart] at this
  obtain ⟨_, hr⟩ := this
  exact hfg hr
